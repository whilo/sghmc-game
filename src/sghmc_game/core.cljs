(ns sghmc-game.core
  (:refer-clojure :exclude [* + - /])
  (:require [play-cljs.core :as p]
            [cljs.reader :refer [read-string]]
            [thinktopic.aljabr.core :as nd]
            [clojure.core.matrix :as m]
            #_[clojure.core.matrix.linear :as ml]
            [thi.ng.typedarrays.core :as a]
            [cljsjs.plotly]

            [thi.ng.geom.viz.core :as viz]
            [thi.ng.geom.svg.core :as svg]
            [thi.ng.geom.core.vector :as v]
            [thi.ng.color.core :as col]
            [thi.ng.math.core :as tm :refer [PI TWO_PI]]
            [thi.ng.math.simplexnoise :as n]

            [cljsjs.react]

            [om.next :as om :refer-macros [defui] :include-macros true]
            [om.dom :as dom :include-macros true]
            [cljs-react-material-ui.core :as ui]
            [sablono.core :refer-macros [html]]))



(enable-console-print!)


;; some aliasing for formula sanity
(def * m/mul)

(def / m/div)

(def + m/add)

(def - m/sub)

(def ** m/pow)

(defn unif [] (.random js/Math))

(def sqrt m/sqrt)

(def log m/log)

(def exp m/exp)


;; some constants
(def cwidth 500)
(def cheight 500)

(def center [(/ cwidth 2) (/ cheight 2)])

(def scale (/ cwidth 10))




;; dear js, when do you finally grow up (standardize)???

(defn nrand
  "Sampling a standard normal univariate variable due to
  https://en.wikipedia.org/wiki/Box%E2%80%93Muller_transform"
  ([]
   (let [u (unif)
         v (unif)]
     (assert (not= u 0))
     (assert (not= v 0))
     (* (sqrt (* -2.0 (log u)))
        (.cos js/Math (* 2.0 PI v)))))
  ([n] (vec (repeatedly n #(nrand)))))

(defn mean [xs]
  (/ (reduce + xs) (count xs)))

(defn sd [xs]
  (let [m (mean xs)]
    (sqrt (/ (reduce (fn [s x] (+ s (** (- m x) 2))) 0 xs)
             (count xs)))))


(comment
  (def foo (repeatedly 10000 #(nrand)))
  (mean foo)
  (sd foo)
  (histogram foo))

;; main algo

(def sghmc-state (atom {}))

(defn sghmc [U gradU m dt nstep x p C V noise-scale]
  (let [p (or p (* (nrand (count x)) (sqrt m)))
        B (* 0.5 V dt)
        D (sqrt (* 2 (- C B) dt))]

    (swap! sghmc-state assoc :p p :B B :D D)
    (loop [i nstep
           x x
           p p]
      (if (pos? i)
        (let [gU (gradU x)
              dx (+ gU (* (nrand (count x)) D))
              p (+ (- p (* dx dt) (* p C (/ dt m)))
                   (* (nrand (count p)) D noise-scale))
              x (+ x (* (/ p m) dt))]
          (swap! sghmc-state assoc :gradU gU :dx dx)
          (recur (dec i) x p))
        [x p]))))


;; plot helpers to verify implementation

(defn histogram
  [id x]
  #_(js/Plotly.newPlot
   id
   (clj->js [{:x x
              :type "histogram"}])
   (clj->js {:margin {:t 0}
             :xaxis {:title "Marginal distribution"}
             })))


(comment
  ;; figure 1 from SGHMC paper, ported from matlab code
  (defn U [x]
    (- (** x 4) (* 2 (** x 2))))

  (defn gradU [x]
    (- (* 4 (** x 3))
       (* 4 x)))


  (def samples
    (loop [nsample 10000
           xs [[0]]]
      (if (pos? nsample)
        (let [m 1
              C 3
              dt 0.1
              nstep 50
              V 4
              next-x (sghmc U gradU m dt nstep (last xs) C V)]
          (recur (dec nsample) (conj xs next-x)))
        xs)))

  (histogram (mapv first samples)))

(defn U-std-norm [x]
  (/ (m/dot x x)
     2))

(exp (- (U-std-norm [1 1])))

(defn U-std-norm-grad [x]
  x)

(U-std-norm-grad [1 1])

(defn U-norm [x mu prec]
  (/ (m/dot (- x mu) (m/mmul prec (- x mu)))
     2))

(defn U-norm-grad [x mu prec]
  (m/mmul prec (- x mu)))

(U-norm [1 1] [0 0] [[0.1 0] [0 0.1]])

(def correlated [[ 27.7777778, -22.2222222],
                 [-22.2222222,  27.7777778]])

(U-norm-grad [1 1] [0 0] correlated)
(defn coord-trafo [scale x]
  (+ (* x scale) center))

(defn inv-coord-trafo [center scale x]
  (/ (- x center) scale))

(defn numer-artif-U [[x y]]
  (* (** (- x 1) y 2)
     (** (+ x 1) y 2)))

(def potentials {0 {:U #(U-norm % [0 0] [[1 0] [0 1]])
                    :Ugrad #(U-norm-grad % [0 0] [[1 0] [0 1]])}
                 1 {:U #(U-norm % [0 0] [[10 9] [9 10]])
                    :Ugrad #(U-norm-grad % [0 0] [[10 9] [9 10]])}
                 2 {:U (fn [[x y]]
                         (+ (* (** (- x 1) 2)
                               (** (- y 2) 2))
                            (* (** (+ x 1) 2)
                               (** (+ y 2) 2))))
                    :Ugrad (fn [[x y]]
                             [(+ (* 2 (- x 1) (** (- y 2) 2))
                                 (* 2 (+ x 1) (** (+ y 2) 2)))
                              (+ (* 2 (- y 2) (** (- x 1) 2))
                                 (* 2 (+ y 2) (** (+ x 1) 2)))])}})


(defonce game (p/create-game cwidth cheight))

(defn update-potential [state]
  (let [{:keys [U Ugrad]} (potentials (-> state :menu :potential-idx))
        cwidth 200
        cheight 200
        scale 20
        potential (vec (for [x (range cwidth)
                             y (range cheight)]
                         [:stroke
                          {:colors [(int (- 255 (* 20 (U (inv-coord-trafo [100 100] scale [x y])))))]}
                          [:point {:x x :y y}]]))]
    (.log js/console "starting potential render")
    (p/pre-render game "potential" cwidth cheight potential)
    (.log js/console "finished potential render")))


(defonce state (atom {:frame-counter 0
                      :sghmc {:pos [1 1]
                              :lr 0.001
                              :m 1
                              :C 3
                              :V 4
                              :noise-scale 1.0}
                      :menu {:lr "0.001"
                             :m "1"
                             :C "3"
                             :V "4"
                             :potential-idx 0
                             :noise-scale "1.0"}
                      :invalid {}
                      :snackbar {:open true
                                 :message "Hello_!"}}))


(defonce main-screen
    (reify p/Screen

      (on-show [this] (update-potential @state)
        #_(reset! state {:pos [-1 -1] :frame-counter 0 :xs []}))

      (on-hide [this])

      (on-render [this]
        (let [xs (get-in @state [:sghmc :xs])]
          (p/render game
                    (let [{{[x y] :pos
                            :keys [lr noise-scale]} :sghmc
                           {:keys [potential-idx]} :menu
                           :keys [frame-counter]} @state
                          {{:keys [U Ugrad]} potential-idx} potentials
                          puck-radius 5
                          [xc yc] (coord-trafo scale [x y])]
                      (when (= (mod frame-counter 10) 0)
                        (histogram "marg-x" (take-last 1000 (take-nth 10 (map first xs))))
                        (histogram "marg-y" (take-last 1000 (take-nth 10 (map second xs)))))
                      (swap! state update :sghmc
                             (fn [{:keys [pos p frame-counter m C V] :as state}]
                               (let [nstep 50
                                     [x p] (sghmc U Ugrad m lr nstep pos p C V noise-scale)]
                                 (-> state
                                     (assoc :pos x :p p)
                                     (update :frame-counter inc)
                                     (update :xs #(conj (or (vec (take-last 3000 %)) []) x))))))
                      [[:image {:name "potential"
                                :x 0 :y 0 :width cwidth :height cheight}]
                       [:fill {:color "white"}
                        [:text {:value (str "x:" (apply str (take 5 (str x))) " "
                                            "y:" (apply str (take 5 (str y))) " ")
                                :x 10
                                :y 20 :size 16 :font "Mono" :style :italic}]]
                       [:stroke {:color "blue"}
                        (let [xs (take-last 200 xs)]
                          (for [[[x1 y1] [x2 y2]]
                                (partition 2 (interleave (map (partial coord-trafo scale) xs)
                                                         (map (partial coord-trafo scale) (rest xs))))]
                            [:line {:x1 x1 :y1 y1 :x2 x2 :y2 y2}]))]
                       [:fill {:color "black"}
                        [:ellipse {:x xc :y yc
                                   :width (* 2 puck-radius) :height (* 2 puck-radius)}]]]
                      ))
          ))))

#_(let [mu (atom [1 1])
      inv-sigma (atom [[10 9] [9 10]])
      U #(U-norm % @mu @inv-sigma)
      #_U #_(fn [[x y]]
          (+ (* (** (- x 1) 2)
                (** (- y 2) 2))
             (* (** (+ x 1) 2)
                (** (+ y 2) 2)))
          #_(+ (** x 2) (** (* (+ x 2) (+ y 2)) 2) (** y 4)))
      Ugrad #(U-norm-grad % @mu @inv-sigma)
      #_Ugrad #_(fn [[x y]]
              [(+ (* 2 (- x 1) (** (- y 2) 2))
                  (* 2 (+ x 1) (** (+ y 2) 2)))
               (+ (* 2 (- y 2) (** (- x 1) 2))
                  (* 2 (+ y 2) (** (+ x 1) 2)))]
              #_[(+ (* 2 x) (* 2 y))
               (+ (* 4 (** y 3)) (* 2 x))])
      dt (atom 0.001)
      high-temp 0.1
      potential (vec (for [x (range cwidth)
                           y (range cheight)]
                       [:stroke
                        {:colors [(int (- 255 (* 20 (U (inv-coord-trafo scale [x y])))))]}
                        [:point {:x x :y y}]]))
      high-potential (vec (for [x (range cwidth)
                                y (range cheight)]
                            [:stroke
                             {:colors [(int (- 255 (* 20 (* high-temp
                                                            (U (inv-coord-trafo scale [x y]))))))]}
                             [:point {:x x :y y}]]))
      lr-input (.getElementById js/document "learning-rate")
      mu-input (.getElementById js/document "mu")
      inv-sigma-input (.getElementById js/document "inv-sigma")]
  (set! (.-onchange lr-input) (fn [_] (reset! dt (read-string (.-value lr-input)))))
  (set! (.-onchange mu-input)
        (fn [_]
          (reset! mu (read-string (.-value mu-input)))
          (let [potential (vec (for [x (range cwidth)
                                     y (range cheight)]
                                 [:stroke
                                  {:colors [(int (- 255 (* 20 (U (inv-coord-trafo scale [x y])))))]}
                                  [:point {:x x :y y}]]))]
            (p/pre-render game "potential" cwidth cheight potential))))
  (set! (.-onchange inv-sigma-input)
        (fn [_]
          (.log js/console (pr-str (read-string (.-value inv-sigma-input))))
          (reset! inv-sigma (read-string (.-value inv-sigma-input)))
          (let [potential (vec (for [x (range cwidth)
                                     y (range cheight)]
                                 [:stroke
                                  {:colors [(int (- 255 (* 20 (U (inv-coord-trafo scale [x y])))))]}
                                  [:point {:x x :y y}]]))]
            (p/pre-render game "potential" cwidth cheight potential))))
  (p/pre-render game "potential" cwidth cheight potential)
  (p/pre-render game "high-potential" cwidth cheight high-potential)
  )

                                        ; start the game









(defn target-val [e]
  (.. e -target -value))

(defn parse-float
  ([cursor e]
   (parse-float cursor e (fn [_])))
  ([cursor e cb]
   (let [nv (target-val e)]
     (swap! state assoc-in (concat [:menu] cursor) nv)
     (try
       (if-let [new (js/parseFloat nv)]
         (if-not (js/isNaN new)
           (do
             (swap! state assoc-in (concat [:sghmc] cursor) new)
             (swap! state assoc-in (concat [:invalid] cursor) nil)
             (cb state))
           (swap! state assoc-in (concat [:invalid] cursor) "This is not a number."))
         (swap! state assoc-in (concat [:invalid] cursor) "Cannot be empty."))
       (catch js/Error e
         (swap! state assoc-in (concat [:invalid] cursor) (ex-message e)))))))



(defui MenuForm
  Object
  (render [this]
          (let [{{:keys [lr mean cov noise-scale potential-idx m C V]} :menu
                 :keys [snackbar] :as cstate} (om/props this)]
            (ui/mui-theme-provider
             {:mui-theme (ui/get-mui-theme (aget js/MaterialUIStyles "DarkRawTheme"))
              #_(ui/get-mui-theme #_{:palette {:text-color "#0000f0"}})}
             (html [:div {:className "col-xs-3"
                          :style {:width "300px"
                                  :position "absolute"
                                  :right "10px"
                                  :top "10px"}}
                    #_(ui/snackbar {:open (:open snackbar)
                                  :message (:message snackbar)
                                  :on-request-close #(swap! state assoc-in [:snackbar :open] false)
                                  :body-style (clj->js {:height :auto
                                                        :lineHeight "20px"
                                                        :color "red"
                                                        :padding "10px"
                                                        :whiteSpace "pre-line"})} [])
                    (ui/paper {:className "pad-20"
                               :rounded true}
                              (ui/drop-down-menu {:value potential-idx
                                                  :className "w-100"
                                                  :on-change (fn [e i v]
                                                               (-> (swap! state assoc-in [:menu :potential-idx] v)
                                                                   update-potential))}
                                                 [(ui/menu-item {:value 0
                                                                 :primary-text "Isotropic Gaussian"})
                                                  (ui/menu-item {:value 1
                                                                 :primary-text "Correlated Gaussian"})
                                                  (ui/menu-item {:value 2
                                                                 :primary-text "Bimodal Non-Gaussian"})])
                              (ui/text-field (merge {:id "m"
                                                     :floating-label-text "Mass"
                                                     :className "w-100"
                                                     :on-change #(parse-float [:m] %)
                                                     :default-value m}
                                                    (when-let [err-txt (get-in cstate [:invalid :m])]
                                                      {:error-text err-txt})))
                              (ui/text-field (merge {:id "C"
                                                     :floating-label-text "C"
                                                     :className "w-100"
                                                     :on-change #(parse-float [:C] %)
                                                     :default-value C}
                                                    (when-let [err-txt (get-in cstate [:invalid :C])]
                                                      {:error-text err-txt})))
                              (ui/text-field (merge {:id "V"
                                                     :floating-label-text "V"
                                                     :className "w-100"
                                                     :on-change #(parse-float [:V] %)
                                                     :default-value V}
                                                    (when-let [err-txt (get-in cstate [:invalid :V])]
                                                      {:error-text err-txt})))
                              (ui/text-field (merge {:id "lr"
                                                     :floating-label-text "Learning rate"
                                                     :className "w-100"
                                                     :on-change #(parse-float [:lr] %)
                                                     :default-value lr}
                                                    (when-let [err-txt (get-in cstate [:invalid :lr])]
                                                      {:error-text err-txt})))
                              (ui/text-field (merge {:id "noise-scale"
                                                     :floating-label-text "Scale noise"
                                                     :className "w-100"
                                                     :on-change #(parse-float [:noise-scale] %)
                                                     :default-value noise-scale}
                                                    (when-let [err-txt (get-in cstate [:invalid :noise-scale])]
                                                      {:error-text err-txt})))
                              )])))))


(def reconciler
  (om/reconciler {:state state}))



(om/add-root! reconciler MenuForm (.getElementById js/document "menu"))

(doto game
  (p/start)
  (p/set-screen main-screen))


(defn on-js-reload []
  ;; optionally touch your app-state to force rerendering depending on
  ;; your application
  (swap! state update-in [:fig-counter] #(inc (or % 0))))




(comment
  (histogram (map first (:xs @state)))
  
  (count (:xs @state))
  (mean (map first (:xs @state)))
  (mean (map second (:xs @state)))


  (sd (map first (:xs @state)))
  (sd (map second (:xs @state)))


  ;; experiments with thi-ng
  (def viz-spec
    {:x-axis (viz/linear-axis
              {:domain [0 63]
               :range  [50 550]
               :major  8
               :minor  2
               :pos    550})
     :y-axis (viz/linear-axis
              {:domain      [0 63]
               :range       [550 50]
               :major       8
               :minor       2
               :pos         50
               :label-dist  15
               :label-style {:text-anchor "end"}})
     :data   [{:matrix       (->> (for [y (range 64) x (range 64)] (n/noise2 (* x 0.06) (* y 0.06)))
                                  (viz/contour-matrix 64 64))
               :levels       (range -1 1 0.05)
               :value-domain [-1.0 1.0]
               :attribs      {:fill "none" :stroke "#0af"}
               :layout       viz/svg-contour-plot}]})

  (def viz-spec-log
    (merge viz-spec
           {:x-axis (viz/log-axis
                     {:domain [0 64]
                      :range [50 550]
                      :base 2
                      :pos 555})
            :y-axis (viz/log-axis
                     {:domain      [0 64]
                      :range       [550 50]
                      :base        2
                      :pos         45
                      :label-dist  15
                      :label-style {:text-anchor "end"}})}))

  (def fill-attribs {:fill (col/rgba 0.0 0.66 1.0 0.05) :stroke "#fff"})

  (defn export-viz
    [viz path] (->> viz
                    (svg/svg {:width 600 :height 600})
                    #_(svg/serialize)
                    #_(spit path)
                    hipo/create
                    (.log js/console)
                    #_(.appendChild js/document.body))
    (->> (hipo/create [:svg/svg
                       [:svg/circle {:r "10"}]
                       [:svg/use {:xlink/href "#id"}]])
         (.log js/console)
         #_(.appendChild js/document.body)
         ))

  (->> {"contours-outline.svg"     [viz-spec false]
        "contours.svg"             [viz-spec true]
        "contours-log-outline.svg" [viz-spec-log false]
        "contours-log.svg"         [viz-spec-log true]}
       (run!
        (fn [[path [spec fill?]]]
          (-> (if fill? (assoc-in spec [:data 0 :attribs] fill-attribs) spec)
              (viz/svg-plot2d-cartesian)
              (export-viz path)))))





  (comment
    (set! (.-innerHTML (.getElementById js/document "marg-x"))
          (hipo/create (->> (viz/svg-plot2d-cartesian viz-spec)
                            (svg/svg {:width 600 :height 600})
                            #_(svg/instance))))

    (hipo/create (->> (viz/svg-plot2d-cartesian viz-spec-log)
                      (svg/svg {:width 600 :height 600})
                      #_(svg/instance)))

    

    )

  )
