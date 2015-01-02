;; Copyright (C) 2013, 2015, Jozef Wagner. All rights reserved.
;;
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0
;; (http://opensource.org/licenses/eclipse-1.0.php) which can be
;; found in the file epl-v10.html at the root of this distribution.
;;
;; By using this software in any fashion, you are agreeing to be bound
;; by the terms of this license.
;;
;; You must not remove this notice, or any other, from this software.

(ns dunaj.resource.serial
  "Serial communication resources based on JSSC.
   Not optimal, mainly due to JSSC limitations, but pretty
   well demostrates many concepts of Dunaj's resources.
   Main jssc limitations: - no flush
                          - cannot query number of breaks and errors
                          - no support for non-blocking writes, nor
                            partial writes (when buf is full)
                          - no io error details (jssc returns false)
                          - unnecessary busy loop in JSSC"
  (:api dunaj)
  (:require
   [dunaj.host.int :refer [Int iint iloop iadd ixFF i0 ior]]
   [dunaj.bit :as bit]
   [dunaj.state :refer [ensure-io ensure-open]]
   [dunaj.coll :refer [IHomogeneous IBatchedRed]]
   [dunaj.coll.helper :refer [reduce-with-batched*]]
   [dunaj.host.array :refer [array byte-array]]
   [dunaj.host.batch :refer [select-item-type provide-batch-size]]
   [dunaj.error :refer [IFailable IFailAware fragile opened-fragile]]
   [dunaj.uri :refer [Uri uri]]
   [dunaj.concurrent.port :refer [ISourcePort IMult -tap! -untap!
                                  -untap-all! chan put! <!! close!]]
   [dunaj.buffer :refer [dropping-buffer]]
   [dunaj.resource :refer
    [IImmutableReadable IReleasable IFlushable IReadable ISeekable
     IAcquirableFactory IWritable IControllable IStatusable]]
   [dunaj.resource.helper :refer [register-factory! defreleasable]]))


;;;; Implementation details

(warn-on-reflection!)

(def ^:private default-serial-batch-size :- Integer
  "Default size for serial port batch."
  8192)

(defn ^:private provide-serial-batch-size :- Integer
  "Returns serial batch size taking into account given
   batch size hint."
  [size-hint :- (Maybe Integer)]
  (provide-batch-size
   (max (or size-hint 0) default-serial-batch-size)))

(deftype ^:private SerialPortResourceReader
  "Reads from the opened serial port."
  [handler :- jssc.SerialPort, resource :- (I IOpenAware IFailable),
   read-ch :- ISourcePort, non-blocking? :- Boolean]
  IRed
  (-reduce [this reducef init]
    (reduce-with-batched* this reducef init))
  IHomogeneous
  (-item-type [this] (keyword->class :byte))
  IBatchedRed
  (-reduce-batched [this requested-type size-hint reducef init]
    (ensure-io)
    (ensure-open resource)
    (let [st (select-item-type requested-type (keyword->class :byte))
          af (fn af [ret wait?]
               (cond
                (reduced? ret) ret
                (postponed? ret)
                (postponed @ret
                           #(throw (unsupported-operation))
                           #(af (unsafe-advance! ret) false))
                wait?
                (postponed ret
                           #(throw (unsupported-operation))
                           #(af ret false))
                (.isOpened handler)
                (let [arr :- (Array java.lang.Byte)
                      (fragile resource (.readBytes handler))]
                  (cond
                   arr (recur
                        (reducef ret (java.nio.ByteBuffer/wrap arr))
                        false)
                   non-blocking? (recur ret true)
                   (<!! read-ch) (recur ret false)
                   :else ret))
                :else ret))]
      (af init false))))

(def ^:private data-bits-map :- {String Integer}
  {"5" 5 "6" 6 "7" 7 "8" 8})

(def ^:private stop-bits-map :- {String Number}
  {"1" 1 "2" 2 "1.5" 1/2})

(def ^:private boolean-map :- {String Boolean}
  {"0" false "1" true "F" false "T" true "false" false "true" true})

(defn ^:private map-value :- Any
  "Returns translated `val` according to `map`,
   if `val` is not empty."
  [val :- Any, map :- {}]
  (when-not (empty? val)
    (or (map val) (throw (illegal-argument val)))))

(defn ^:private uri->map :- KeywordMap
  "Returns settings map based on given uri."
  [x :- (U String Uri)]
  (let [uri (uri x)
        scheme (.getScheme ^java.net.URI uri)
        ssp (.getSchemeSpecificPart ^java.net.URI uri)
        [port baud-rate data-bits stop-bits parity flow dtr rts]
        (seq (take-nth 2 (parse #"[^:]*" ssp)))]
    (when-not (or (empty? scheme) (= scheme "serial"))
      (throw (illegal-argument "scheme")))
    {:port (when-not (empty? port) port)
     :baud-rate (when-not (empty? baud-rate)
                  (java.lang.Integer/valueOf
                   ^java.lang.String baud-rate))
     :data-bits (map-value data-bits data-bits-map)
     :stop-bits (map-value stop-bits stop-bits-map)
     :parity (when-not (empty? parity) (keyword parity))
     :flow-mode (when-not (empty? flow) (keyword flow))
     :init-dtr (map-value dtr boolean-map)
     :init-rts (map-value rts boolean-map)}))

(defn ^:private map->uri :- Uri
  "Returns canonical serial port uri based on given map."
  [map :- KeywordMap]
  (let [sbf #(cond (== 1 %) "1" (== 2 %) "2" (< 1.499 % 1.501) "1.5"
                   :else (throw (illegal-argument "stop bits")))
        {:keys [port baud-rate data-bits stop-bits
                parity flow-mode init-dtr init-rts]} map]
    (java.net.URI. "serial"
                   (->str
                    port
                    ":" (if (nil? baud-rate) "" baud-rate)
                    ":" (if (nil? data-bits) "" data-bits)
                    ":" (if (nil? stop-bits) "" (sbf stop-bits))
                    ":" (if (nil? parity) "" (name parity))
                    ":" (if (nil? flow-mode) "" (name flow-mode))
                    ":" (if (nil? init-dtr) "" init-dtr)
                    ":" (if (nil? init-rts) "" init-rts))
                   nil)))

(defprotocol ^:private ISerialPort
  (-set-dtr! :- nil [this val :- Boolean])
  (-set-rts! :- nil [this val :- Boolean])
  (-purge! :- nil [this opts :- IRed])
  (-break! :- nil [this duration-ms :- Integer])
  (-update-status! :- nil [this]))

(defn ^:private byte-batch->array :- (Array java.lang.Byte)
  "Returns array for a given byte `batch`"
  [batch :- (Batch java.lang.Byte)]
  (if (and (.hasArray batch) (zero? (.position batch))
           (== (.limit batch) (.capacity batch)))
    (.array batch)
    (let [l (.remaining batch)
          arr (byte-array l)
          oldpos (.position batch)]
      (.get batch arr (i0) l)
      (.position batch oldpos)
      arr)))

(defmacro ^:private ensure-serial-io
  [handler exp msg]
  `(when-not ~exp (.closePort ~handler) (throw (io ~msg))))

(defmacro ^:private ensure-serial-control
  [resource handler ice exp msg]
  `(opened-fragile ~resource
                   (when-not (or ~exp ~ice)
                     (.closePort ~handler)
                     (throw (io ~msg)))))

(defreleasable ^:private SerialPortResource
  "Serial resource type."
  [handler :- jssc.SerialPort, config :- {},
   ^:unsynchronized-mutable dtr :- Boolean,
   ^:volatile-mutable rts :- Boolean,
   ignore-control-errors :- Boolean, batch-size :- (Maybe Integer),
   status-ref :- IReference, read-ch :- ISourcePort,
   ^:volatile-mutable error :- (Maybe IException),
   ^:volatile-mutable non-blocking? :- Boolean]
  ;; NOTE: No flush, as jssc does not provide it either
  IConfig
  (-config [this] config)
  IOpenAware
  (-open? [this] (and (nil? error) (.isOpened handler)))
  IFailAware
  (-error [this] error)
  IFailable
  (-fail! [this ex] (when (nil? error) (set! error ex)) nil)
  IReleasable
  (-release! [this]
    (close! read-ch)
    (fragile this (when (.isOpened handler) (.closePort handler)))
    nil)
  ISerialPort
  (-set-dtr! [this val]
    (when-not (or (nil? val) (boolean? val))
      (throw (illegal-argument "dtr")))
    (set! dtr (boolean val))
    (ensure-serial-control this handler ignore-control-errors
                           (.setDTR handler (boolean val))
                           "cannot set dtr")
    nil)
  (-set-rts! [this val]
    (when-not (or (nil? val) (boolean? val))
      (throw (illegal-argument "rts")))
    (set! rts (boolean val))
    (ensure-serial-control this handler ignore-control-errors
                           (.setRTS handler (boolean val))
                           "cannot set rts")
    nil)
  (-purge! [this opts]
    (let [rf (fn [flag opt]
               (ior
                flag
                (condp identical? opt
                  :all (ior
                        jssc.SerialPort/PURGE_RXCLEAR
                        (ior
                         jssc.SerialPort/PURGE_TXCLEAR
                         (ior
                          jssc.SerialPort/PURGE_RXABORT
                          jssc.SerialPort/PURGE_TXABORT)))
                  :in (ior jssc.SerialPort/PURGE_RXCLEAR
                           jssc.SerialPort/PURGE_RXABORT)
                  :out (ior jssc.SerialPort/PURGE_TXCLEAR
                            jssc.SerialPort/PURGE_TXABORT)
                  :buffer (ior jssc.SerialPort/PURGE_RXCLEAR
                               jssc.SerialPort/PURGE_TXCLEAR)
                  :abort (ior jssc.SerialPort/PURGE_RXABORT
                              jssc.SerialPort/PURGE_TXABORT)
                  :in-buffer jssc.SerialPort/PURGE_RXCLEAR
                  :out-buffer jssc.SerialPort/PURGE_TXCLEAR
                  :in-abort jssc.SerialPort/PURGE_RXABORT
                  :out-abort jssc.SerialPort/PURGE_TXABORT)))
          flags (reduce rf (i0) opts)]
      (ensure-serial-control this handler ignore-control-errors
                             (.purgePort handler flags)
                             "cannot purge"))
    nil)
  (-break! [this duration-ms]
    (ensure-serial-control this handler ignore-control-errors
                           (.sendBreak handler duration-ms)
                           "cannot send break")
    nil)
  (-update-status! [this]
    (opened-fragile this
      (reset! status-ref
              {;;:in-bytes (.getInputBufferBytesCount handler)
               ;;:out-bytes (.getOutputBufferBytesCount handler)
               :cts (.isCTS handler)
               :dsr (.isDSR handler)
               :ring (.isRING handler)
               :dcd (.isRLSD handler)}))
    nil)
  IStatusable
  (-status [this]
    ;; NOTE: errors and breaks are not included,
    ;;       this is a jssc limitation which is not trivial to fix
    (-update-status! this)
    (reify
      IReference
      (-deref [_] (ensure-open this) @status-ref)
      IMult
      (-tap! [m ch close?] (-tap! status-ref ch close?))
      (-untap! [m ch] (-untap! status-ref ch))
      (-untap-all! [m] (-untap-all! status-ref))))
  IControllable
  (-controller [this]
    (ensure-open this)
    (reify
      IReference
      (-deref [_]
        (ensure-open this)
        {:dtr (.-dtr this) :rts (.-rts this)})
      IMutable
      (-reset! [inthis m]
        (when-not (every? #(contains? m %) [:dtr :rts])
          (throw (illegal-argument "missing keys")))
        (reduce (fn [r [k v]] (adjust! r k v)) inthis m)
        m)
      IAdjustable
      (-adjust! [inthis k v]
        (cond (identical? k :dtr) (-set-dtr! this v)
              (identical? k :rts) (-set-rts! this v)
              :else (throw (illegal-argument (->str k))))
        inthis)))
  IReadable
  (-read! [this]
    (->SerialPortResourceReader handler this read-ch non-blocking?))
  IWritable
  (-write! [this coll]
    (ensure-open this)
    (reduce-batched
     (keyword->class :byte) batch-size
     (fn rf [ret :- Any, batch :- (Batch java.lang.Byte)]
       (let [arr (byte-batch->array batch)]
         ;; NOTE: cannot retry and does not support non-blocking mode,
         ;;       this is a limitation of jssc
         (fragile this (ensure-serial-io handler
                                         (.writeBytes handler arr)
                                         "write error"))
         (iadd ret (.remaining batch))))
     (i0) coll)))

(defn stop-bits->jssc :- Int
  [stop-bits :- Number]
  (iint (cond (== stop-bits 1) jssc.SerialPort/STOPBITS_1
              (== stop-bits 2) jssc.SerialPort/STOPBITS_2
              (< 1.499 stop-bits 1.501) jssc.SerialPort/STOPBITS_1_5
              :else (throw (illegal-argument "unknown stop bits")))))

(defn parity->jssc :- Int
  [parity :- (Maybe Keyword)]
  (iint (cond (or (nil? parity) (identical? parity :none))
              jssc.SerialPort/PARITY_NONE
              (identical? parity :even) jssc.SerialPort/PARITY_EVEN
              (identical? parity :odd) jssc.SerialPort/PARITY_ODD
              (identical? parity :mark) jssc.SerialPort/PARITY_MARK
              (identical? parity :space) jssc.SerialPort/PARITY_SPACE
              :else (throw (illegal-argument "unknown parity")))))

(defn flow-mode->jssc :- Int
  [mode :- (Maybe Keyword)]
  (iint (cond (or (nil? mode) (identical? mode :none))
              jssc.SerialPort/FLOWCONTROL_NONE
              (identical? mode :hardware-in)
              jssc.SerialPort/FLOWCONTROL_RTSCTS_IN
              (identical? mode :hardware-out)
              jssc.SerialPort/FLOWCONTROL_RTSCTS_OUT
              (identical? mode :hardware)
              (ior jssc.SerialPort/FLOWCONTROL_RTSCTS_IN
                   jssc.SerialPort/FLOWCONTROL_RTSCTS_OUT)
              (identical? mode :software-in)
              jssc.SerialPort/FLOWCONTROL_XONXOFF_IN
              (identical? mode :software-out)
              jssc.SerialPort/FLOWCONTROL_XONXOFF_OUT
              (identical? mode :software)
              (ior jssc.SerialPort/FLOWCONTROL_XONXOFF_IN
                   jssc.SerialPort/FLOWCONTROL_XONXOFF_OUT)
              :else (throw (illegal-argument "unknown flow mode")))))

(defrecord SerialPortResourceFactory
  "Factory type for resources for serial communication."
  [uri port baud-rate data-bits stop-bits parity flow-mode
   init-dtr init-rts ignore-control-errors batch-size non-blocking?]
  IAcquirableFactory
  (-acquire! [this]
    (let [um (uri->map uri)
          batch-size (provide-serial-batch-size batch-size)
          config (merge-with #(if (nil? %2) % %2) this um)
          config (assoc config :uri (map->uri config))
          handler (jssc.SerialPort. (:port config))
          {:keys [baud-rate data-bits stop-bits parity flow-mode
                  init-dtr init-rts]} config]
      (when-not (.openPort handler)
        (throw (illegal-state "cannot open port")))
      (ensure-serial-io handler
                        (or (.setParams handler (iint baud-rate)
                                        (iint data-bits)
                                        (stop-bits->jssc stop-bits)
                                        (parity->jssc parity)
                                        (boolean init-dtr)
                                        (boolean init-rts))
                            ignore-control-errors)
                        "cannot set params for port")
      (ensure-serial-io handler
                        (or (.setFlowControlMode
                             handler (flow-mode->jssc flow-mode))
                            ignore-control-errors)
                        "cannot ser flow control mode")
      (ensure-serial-io handler
                        (or (.purgePort
                             handler
                             (bit/or jssc.SerialPort/PURGE_RXABORT
                                     jssc.SerialPort/PURGE_TXABORT
                                     jssc.SerialPort/PURGE_RXCLEAR
                                     jssc.SerialPort/PURGE_TXCLEAR))
                            ignore-control-errors)
                        "cannot purge port")
      (let [read-ch (chan (dropping-buffer 1))
            res (->SerialPortResource
                 handler config (boolean init-dtr)
                 (boolean init-rts) ignore-control-errors batch-size
                 (atom {}) read-ch nil (boolean non-blocking?))
            callback (reify
                       jssc.SerialPortEventListener
                       (serialEvent [this ev]
                         (let [evt (.getEventType ev)]
                           (if (== evt jssc.SerialPortEvent/RXCHAR)
                             (do (put! read-ch true)
                                 ;; slow down jssc listener
                                 (java.lang.Thread/sleep 100))
                             (-update-status! res)))))]
        (.addEventListener ^jssc.SerialPort handler
                           ^jssc.SerialPortEventListener callback
                           (bit/or jssc.SerialPort/MASK_CTS
                                   jssc.SerialPort/MASK_DSR
                                   jssc.SerialPort/MASK_RING
                                   jssc.SerialPort/MASK_RLSD
                                   ;;jssc.SerialPort/MASK_ERR
                                   ;;jssc.SerialPort/MASK_TXEMPTY
                                   jssc.SerialPort/MASK_RXCHAR))
        ;; must sleep to give time for event listener to kick in
        (java.lang.Thread/sleep 10)
        res))))


;;;; Public API

(def serial-factory :- SerialPortResourceFactory
  "Serial port resource factory.
   Current options are:

   uri port baud-rate data-bits stop-bits parity flow-mode
   init-dtr init-rts ignore-control-errors batch-size non-blocking?"
  {:added "1.0"}
  (->SerialPortResourceFactory
   nil nil 9600 8 1 :none :none true true true nil false))

(defn serial :- SerialPortResourceFactory
  "Returns serial port resource factory with given
   `_uri_` and `_opts_` set."
  {:added "1.0"}
  [uri :- (U nil String Uri) & {:as opts}]
  (merge serial-factory (assoc opts :uri uri)))

(defn purge! :- nil
  "Purges buffers and pending operations, based on given `_opts_`.
   Valid options are `:all` `:in` `:out` `:buffer` `:abort`
   `:in-buffer` `:out-buffer` `:in-abort` `:out-abort`."
  {:added "1.0"}
  [res :- SerialPortResource & opts :- Keyword]
  (-purge! res (if (empty? opts) [:all] opts)))

(defn break! :- nil
  "Sends break signal to the serial port `_res_` for the `_duration_`.
   Blocks until operation is done. Duration may be ignored in some
   OSs."
  {:added "1.0"}
  [res :- SerialPortResource, duration :- (U nil Integer IDuration)]
  (-break! res (milliseconds duration)))

(register-factory! "serial" serial-factory)
