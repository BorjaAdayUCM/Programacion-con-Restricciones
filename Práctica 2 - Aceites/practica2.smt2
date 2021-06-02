(set-option :produce-models true)
(set-logic QF_LIA)
(declare-fun beneficio () Int)
(declare-fun compras_0_0 () Int)
(declare-fun refinado_0_0 () Int)
(declare-fun compras_0_1 () Int)
(declare-fun refinado_0_1 () Int)
(declare-fun compras_0_2 () Int)
(declare-fun refinado_0_2 () Int)
(declare-fun compras_0_3 () Int)
(declare-fun refinado_0_3 () Int)
(declare-fun compras_0_4 () Int)
(declare-fun refinado_0_4 () Int)
(declare-fun compras_1_0 () Int)
(declare-fun refinado_1_0 () Int)
(declare-fun compras_1_1 () Int)
(declare-fun refinado_1_1 () Int)
(declare-fun compras_1_2 () Int)
(declare-fun refinado_1_2 () Int)
(declare-fun compras_1_3 () Int)
(declare-fun refinado_1_3 () Int)
(declare-fun compras_1_4 () Int)
(declare-fun refinado_1_4 () Int)
(declare-fun compras_2_0 () Int)
(declare-fun refinado_2_0 () Int)
(declare-fun compras_2_1 () Int)
(declare-fun refinado_2_1 () Int)
(declare-fun compras_2_2 () Int)
(declare-fun refinado_2_2 () Int)
(declare-fun compras_2_3 () Int)
(declare-fun refinado_2_3 () Int)
(declare-fun compras_2_4 () Int)
(declare-fun refinado_2_4 () Int)
(declare-fun compras_3_0 () Int)
(declare-fun refinado_3_0 () Int)
(declare-fun compras_3_1 () Int)
(declare-fun refinado_3_1 () Int)
(declare-fun compras_3_2 () Int)
(declare-fun refinado_3_2 () Int)
(declare-fun compras_3_3 () Int)
(declare-fun refinado_3_3 () Int)
(declare-fun compras_3_4 () Int)
(declare-fun refinado_3_4 () Int)
(declare-fun compras_4_0 () Int)
(declare-fun refinado_4_0 () Int)
(declare-fun compras_4_1 () Int)
(declare-fun refinado_4_1 () Int)
(declare-fun compras_4_2 () Int)
(declare-fun refinado_4_2 () Int)
(declare-fun compras_4_3 () Int)
(declare-fun refinado_4_3 () Int)
(declare-fun compras_4_4 () Int)
(declare-fun refinado_4_4 () Int)
(declare-fun compras_5_0 () Int)
(declare-fun refinado_5_0 () Int)
(declare-fun compras_5_1 () Int)
(declare-fun refinado_5_1 () Int)
(declare-fun compras_5_2 () Int)
(declare-fun refinado_5_2 () Int)
(declare-fun compras_5_3 () Int)
(declare-fun refinado_5_3 () Int)
(declare-fun compras_5_4 () Int)
(declare-fun refinado_5_4 () Int)
(assert (and (>= compras_0_0 0 ) (>= refinado_0_0 0 ) ) )
(assert (and (>= compras_0_1 0 ) (>= refinado_0_1 0 ) ) )
(assert (and (>= compras_0_2 0 ) (>= refinado_0_2 0 ) ) )
(assert (and (>= compras_0_3 0 ) (>= refinado_0_3 0 ) ) )
(assert (and (>= compras_0_4 0 ) (>= refinado_0_4 0 ) ) )
(assert (and (>= compras_1_0 0 ) (>= refinado_1_0 0 ) ) )
(assert (and (>= compras_1_1 0 ) (>= refinado_1_1 0 ) ) )
(assert (and (>= compras_1_2 0 ) (>= refinado_1_2 0 ) ) )
(assert (and (>= compras_1_3 0 ) (>= refinado_1_3 0 ) ) )
(assert (and (>= compras_1_4 0 ) (>= refinado_1_4 0 ) ) )
(assert (and (>= compras_2_0 0 ) (>= refinado_2_0 0 ) ) )
(assert (and (>= compras_2_1 0 ) (>= refinado_2_1 0 ) ) )
(assert (and (>= compras_2_2 0 ) (>= refinado_2_2 0 ) ) )
(assert (and (>= compras_2_3 0 ) (>= refinado_2_3 0 ) ) )
(assert (and (>= compras_2_4 0 ) (>= refinado_2_4 0 ) ) )
(assert (and (>= compras_3_0 0 ) (>= refinado_3_0 0 ) ) )
(assert (and (>= compras_3_1 0 ) (>= refinado_3_1 0 ) ) )
(assert (and (>= compras_3_2 0 ) (>= refinado_3_2 0 ) ) )
(assert (and (>= compras_3_3 0 ) (>= refinado_3_3 0 ) ) )
(assert (and (>= compras_3_4 0 ) (>= refinado_3_4 0 ) ) )
(assert (and (>= compras_4_0 0 ) (>= refinado_4_0 0 ) ) )
(assert (and (>= compras_4_1 0 ) (>= refinado_4_1 0 ) ) )
(assert (and (>= compras_4_2 0 ) (>= refinado_4_2 0 ) ) )
(assert (and (>= compras_4_3 0 ) (>= refinado_4_3 0 ) ) )
(assert (and (>= compras_4_4 0 ) (>= refinado_4_4 0 ) ) )
(assert (and (>= compras_5_0 0 ) (>= refinado_5_0 0 ) ) )
(assert (and (>= compras_5_1 0 ) (>= refinado_5_1 0 ) ) )
(assert (and (>= compras_5_2 0 ) (>= refinado_5_2 0 ) ) )
(assert (and (>= compras_5_3 0 ) (>= refinado_5_3 0 ) ) )
(assert (and (>= compras_5_4 0 ) (>= refinado_5_4 0 ) ) )
(assert (<= refinado_0_0 compras_0_0 ) )
(assert (<= refinado_0_1 compras_0_1 ) )
(assert (<= refinado_0_2 compras_0_2 ) )
(assert (<= refinado_0_3 compras_0_3 ) )
(assert (<= refinado_0_4 compras_0_4 ) )
(assert (<= refinado_1_0 (+ (- compras_0_0 refinado_0_0 ) compras_1_0 ) ) )
(assert (<= refinado_1_1 (+ (- compras_0_1 refinado_0_1 ) compras_1_1 ) ) )
(assert (<= refinado_1_2 (+ (- compras_0_2 refinado_0_2 ) compras_1_2 ) ) )
(assert (<= refinado_1_3 (+ (- compras_0_3 refinado_0_3 ) compras_1_3 ) ) )
(assert (<= refinado_1_4 (+ (- compras_0_4 refinado_0_4 ) compras_1_4 ) ) )
(assert (<= refinado_2_0 (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_2_0 ) ) ) )
(assert (<= refinado_2_1 (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_2_1 ) ) ) )
(assert (<= refinado_2_2 (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_2_2 ) ) ) )
(assert (<= refinado_2_3 (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_2_3 ) ) ) )
(assert (<= refinado_2_4 (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_2_4 ) ) ) )
(assert (<= refinado_3_0 (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_3_0 ) ) ) ) )
(assert (<= refinado_3_1 (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_3_1 ) ) ) ) )
(assert (<= refinado_3_2 (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_3_2 ) ) ) ) )
(assert (<= refinado_3_3 (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_3_3 ) ) ) ) )
(assert (<= refinado_3_4 (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_3_4 ) ) ) ) )
(assert (<= refinado_4_0 (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_4_0 ) ) ) ) ) )
(assert (<= refinado_4_1 (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_4_1 ) ) ) ) ) )
(assert (<= refinado_4_2 (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_4_2 ) ) ) ) ) )
(assert (<= refinado_4_3 (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_4_3 ) ) ) ) ) )
(assert (<= refinado_4_4 (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_4_4 ) ) ) ) ) )
(assert (<= refinado_5_0 (+ (- compras_4_0 refinado_4_0 ) (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_5_0 ) ) ) ) ) ) )
(assert (<= refinado_5_1 (+ (- compras_4_1 refinado_4_1 ) (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_5_1 ) ) ) ) ) ) )
(assert (<= refinado_5_2 (+ (- compras_4_2 refinado_4_2 ) (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_5_2 ) ) ) ) ) ) )
(assert (<= refinado_5_3 (+ (- compras_4_3 refinado_4_3 ) (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_5_3 ) ) ) ) ) ) )
(assert (<= refinado_5_4 (+ (- compras_4_4 refinado_4_4 ) (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_5_4 ) ) ) ) ) ) )
(assert (and (<= (+ refinado_0_1 refinado_0_0 ) 200 ) (<= (+ refinado_0_4 (+ refinado_0_3 refinado_0_2 ) ) 250 ) ) )
(assert (and (<= (+ refinado_1_1 refinado_1_0 ) 200 ) (<= (+ refinado_1_4 (+ refinado_1_3 refinado_1_2 ) ) 250 ) ) )
(assert (and (<= (+ refinado_2_1 refinado_2_0 ) 200 ) (<= (+ refinado_2_4 (+ refinado_2_3 refinado_2_2 ) ) 250 ) ) )
(assert (and (<= (+ refinado_3_1 refinado_3_0 ) 200 ) (<= (+ refinado_3_4 (+ refinado_3_3 refinado_3_2 ) ) 250 ) ) )
(assert (and (<= (+ refinado_4_1 refinado_4_0 ) 200 ) (<= (+ refinado_4_4 (+ refinado_4_3 refinado_4_2 ) ) 250 ) ) )
(assert (and (<= (+ refinado_5_1 refinado_5_0 ) 200 ) (<= (+ refinado_5_4 (+ refinado_5_3 refinado_5_2 ) ) 250 ) ) )
(assert (<= compras_0_0 1000 ) )
(assert (<= compras_0_1 1000 ) )
(assert (<= compras_0_2 1000 ) )
(assert (<= compras_0_3 1000 ) )
(assert (<= compras_0_4 1000 ) )
(assert (<= (+ (- compras_0_0 refinado_0_0 ) compras_1_0 ) 1000 ) )
(assert (<= (+ (- compras_0_1 refinado_0_1 ) compras_1_1 ) 1000 ) )
(assert (<= (+ (- compras_0_2 refinado_0_2 ) compras_1_2 ) 1000 ) )
(assert (<= (+ (- compras_0_3 refinado_0_3 ) compras_1_3 ) 1000 ) )
(assert (<= (+ (- compras_0_4 refinado_0_4 ) compras_1_4 ) 1000 ) )
(assert (<= (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_2_0 ) ) 1000 ) )
(assert (<= (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_2_1 ) ) 1000 ) )
(assert (<= (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_2_2 ) ) 1000 ) )
(assert (<= (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_2_3 ) ) 1000 ) )
(assert (<= (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_2_4 ) ) 1000 ) )
(assert (<= (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_3_0 ) ) ) 1000 ) )
(assert (<= (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_3_1 ) ) ) 1000 ) )
(assert (<= (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_3_2 ) ) ) 1000 ) )
(assert (<= (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_3_3 ) ) ) 1000 ) )
(assert (<= (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_3_4 ) ) ) 1000 ) )
(assert (<= (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_4_0 ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_4_1 ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_4_2 ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_4_3 ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_4_4 ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_4_0 refinado_4_0 ) (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) compras_5_0 ) ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_4_1 refinado_4_1 ) (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) compras_5_1 ) ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_4_2 refinado_4_2 ) (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) compras_5_2 ) ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_4_3 refinado_4_3 ) (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) compras_5_3 ) ) ) ) ) 1000 ) )
(assert (<= (+ (- compras_4_4 refinado_4_4 ) (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) compras_5_4 ) ) ) ) ) 1000 ) )
(assert (= (+ (- compras_5_0 refinado_5_0 ) (+ (- compras_4_0 refinado_4_0 ) (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (- compras_0_0 refinado_0_0 ) ) ) ) ) ) 11 ) )
(assert (= (+ (- compras_5_1 refinado_5_1 ) (+ (- compras_4_1 refinado_4_1 ) (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (- compras_0_1 refinado_0_1 ) ) ) ) ) ) 3 ) )
(assert (= (+ (- compras_5_2 refinado_5_2 ) (+ (- compras_4_2 refinado_4_2 ) (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (- compras_0_2 refinado_0_2 ) ) ) ) ) ) 7 ) )
(assert (= (+ (- compras_5_3 refinado_5_3 ) (+ (- compras_4_3 refinado_4_3 ) (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (- compras_0_3 refinado_0_3 ) ) ) ) ) ) 9 ) )
(assert (= (+ (- compras_5_4 refinado_5_4 ) (+ (- compras_4_4 refinado_4_4 ) (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (- compras_0_4 refinado_0_4 ) ) ) ) ) ) 12 ) )
(assert (and (<= (+ (* refinado_0_4 50 ) (+ (* refinado_0_3 42 ) (+ (* refinado_0_2 20 ) (+ (* refinado_0_1 61 ) (* refinado_0_0 88 ) ) ) ) ) (* 60 (+ refinado_0_4 (+ refinado_0_3 (+ refinado_0_2 (+ refinado_0_1 refinado_0_0 ) ) ) ) ) ) (>= (* refinado_0_0 88 ) (* 30 refinado_0_0 ) ) ) )
(assert (and (<= (+ (* refinado_1_4 50 ) (+ (* refinado_1_3 42 ) (+ (* refinado_1_2 20 ) (+ (* refinado_1_1 61 ) (* refinado_1_0 88 ) ) ) ) ) (* 60 (+ refinado_1_4 (+ refinado_1_3 (+ refinado_1_2 (+ refinado_1_1 refinado_1_0 ) ) ) ) ) ) (>= (* refinado_1_0 88 ) (* 30 refinado_1_0 ) ) ) )
(assert (and (<= (+ (* refinado_2_4 50 ) (+ (* refinado_2_3 42 ) (+ (* refinado_2_2 20 ) (+ (* refinado_2_1 61 ) (* refinado_2_0 88 ) ) ) ) ) (* 60 (+ refinado_2_4 (+ refinado_2_3 (+ refinado_2_2 (+ refinado_2_1 refinado_2_0 ) ) ) ) ) ) (>= (* refinado_2_0 88 ) (* 30 refinado_2_0 ) ) ) )
(assert (and (<= (+ (* refinado_3_4 50 ) (+ (* refinado_3_3 42 ) (+ (* refinado_3_2 20 ) (+ (* refinado_3_1 61 ) (* refinado_3_0 88 ) ) ) ) ) (* 60 (+ refinado_3_4 (+ refinado_3_3 (+ refinado_3_2 (+ refinado_3_1 refinado_3_0 ) ) ) ) ) ) (>= (* refinado_3_0 88 ) (* 30 refinado_3_0 ) ) ) )
(assert (and (<= (+ (* refinado_4_4 50 ) (+ (* refinado_4_3 42 ) (+ (* refinado_4_2 20 ) (+ (* refinado_4_1 61 ) (* refinado_4_0 88 ) ) ) ) ) (* 60 (+ refinado_4_4 (+ refinado_4_3 (+ refinado_4_2 (+ refinado_4_1 refinado_4_0 ) ) ) ) ) ) (>= (* refinado_4_0 88 ) (* 30 refinado_4_0 ) ) ) )
(assert (and (<= (+ (* refinado_5_4 50 ) (+ (* refinado_5_3 42 ) (+ (* refinado_5_2 20 ) (+ (* refinado_5_1 61 ) (* refinado_5_0 88 ) ) ) ) ) (* 60 (+ refinado_5_4 (+ refinado_5_3 (+ refinado_5_2 (+ refinado_5_1 refinado_5_0 ) ) ) ) ) ) (>= (* refinado_5_0 88 ) (* 30 refinado_5_0 ) ) ) )
(assert (= beneficio (- (+ (* refinado_5_4 150 ) (+ (* refinado_5_3 150 ) (+ (* refinado_5_2 150 ) (+ (* refinado_5_1 150 ) (+ (* refinado_5_0 150 ) (+ (* refinado_4_4 150 ) (+ (* refinado_4_3 150 ) (+ (* refinado_4_2 150 ) (+ (* refinado_4_1 150 ) (+ (* refinado_4_0 150 ) (+ (* refinado_3_4 150 ) (+ (* refinado_3_3 150 ) (+ (* refinado_3_2 150 ) (+ (* refinado_3_1 150 ) (+ (* refinado_3_0 150 ) (+ (* refinado_2_4 150 ) (+ (* refinado_2_3 150 ) (+ (* refinado_2_2 150 ) (+ (* refinado_2_1 150 ) (+ (* refinado_2_0 150 ) (+ (* refinado_1_4 150 ) (+ (* refinado_1_3 150 ) (+ (* refinado_1_2 150 ) (+ (* refinado_1_1 150 ) (+ (* refinado_1_0 150 ) (+ (* refinado_0_4 150 ) (+ (* refinado_0_3 150 ) (+ (* refinado_0_2 150 ) (+ (* refinado_0_1 150 ) (* refinado_0_0 150 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) (+ (+ (* compras_5_4 135 ) (+ (* compras_5_3 80 ) (+ (* compras_5_2 140 ) (+ (* compras_5_1 100 ) (+ (* compras_5_0 90 ) (+ (* compras_4_4 105 ) (+ (* compras_4_3 110 ) (+ (* compras_4_2 150 ) (+ (* compras_4_1 120 ) (+ (* compras_4_0 100 ) (+ (* compras_3_4 125 ) (+ (* compras_3_3 120 ) (+ (* compras_3_2 120 ) (+ (* compras_3_1 110 ) (+ (* compras_3_0 120 ) (+ (* compras_2_4 95 ) (+ (* compras_2_3 100 ) (+ (* compras_2_2 130 ) (+ (* compras_2_1 140 ) (+ (* compras_2_0 110 ) (+ (* compras_1_4 115 ) (+ (* compras_1_3 90 ) (+ (* compras_1_2 110 ) (+ (* compras_1_1 130 ) (+ (* compras_1_0 130 ) (+ (* compras_0_4 115 ) (+ (* compras_0_3 110 ) (+ (* compras_0_2 130 ) (+ (* compras_0_1 120 ) (* compras_0_0 110 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) (* (+ (- compras_4_4 refinado_4_4 ) (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) (+ compras_5_4 (+ (- compras_4_3 refinado_4_3 ) (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) (+ compras_5_3 (+ (- compras_4_2 refinado_4_2 ) (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) (+ compras_5_2 (+ (- compras_4_1 refinado_4_1 ) (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) (+ compras_5_1 (+ (- compras_4_0 refinado_4_0 ) (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) (+ compras_5_0 (+ (- compras_3_4 refinado_3_4 ) (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) (+ compras_4_4 (+ (- compras_3_3 refinado_3_3 ) (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) (+ compras_4_3 (+ (- compras_3_2 refinado_3_2 ) (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) (+ compras_4_2 (+ (- compras_3_1 refinado_3_1 ) (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) (+ compras_4_1 (+ (- compras_3_0 refinado_3_0 ) (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) (+ compras_4_0 (+ (- compras_2_4 refinado_2_4 ) (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) (+ compras_3_4 (+ (- compras_2_3 refinado_2_3 ) (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) (+ compras_3_3 (+ (- compras_2_2 refinado_2_2 ) (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) (+ compras_3_2 (+ (- compras_2_1 refinado_2_1 ) (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) (+ compras_3_1 (+ (- compras_2_0 refinado_2_0 ) (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) (+ compras_3_0 (+ (- compras_1_4 refinado_1_4 ) (+ (- compras_0_4 refinado_0_4 ) (+ compras_2_4 (+ (- compras_1_3 refinado_1_3 ) (+ (- compras_0_3 refinado_0_3 ) (+ compras_2_3 (+ (- compras_1_2 refinado_1_2 ) (+ (- compras_0_2 refinado_0_2 ) (+ compras_2_2 (+ (- compras_1_1 refinado_1_1 ) (+ (- compras_0_1 refinado_0_1 ) (+ compras_2_1 (+ (- compras_1_0 refinado_1_0 ) (+ (- compras_0_0 refinado_0_0 ) (+ compras_2_0 (+ (- compras_0_4 refinado_0_4 ) (+ compras_1_4 (+ (- compras_0_3 refinado_0_3 ) (+ compras_1_3 (+ (- compras_0_2 refinado_0_2 ) (+ compras_1_2 (+ (- compras_0_1 refinado_0_1 ) (+ compras_1_1 (+ (- compras_0_0 refinado_0_0 ) (+ compras_1_0 (+ compras_0_4 (+ compras_0_3 (+ compras_0_2 (+ compras_0_1 compras_0_0 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) 2 ) ) ) ) )
(assert (>= beneficio 100000 ) )
(assert-soft (<= (+ (ite (> refinado_0_4 0 ) 1 0 ) (+ (ite (> refinado_0_3 0 ) 1 0 ) (+ (ite (> refinado_0_2 0 ) 1 0 ) (+ (ite (> refinado_0_1 0 ) 1 0 ) (ite (> refinado_0_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (<= (+ (ite (> refinado_1_4 0 ) 1 0 ) (+ (ite (> refinado_1_3 0 ) 1 0 ) (+ (ite (> refinado_1_2 0 ) 1 0 ) (+ (ite (> refinado_1_1 0 ) 1 0 ) (ite (> refinado_1_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (<= (+ (ite (> refinado_2_4 0 ) 1 0 ) (+ (ite (> refinado_2_3 0 ) 1 0 ) (+ (ite (> refinado_2_2 0 ) 1 0 ) (+ (ite (> refinado_2_1 0 ) 1 0 ) (ite (> refinado_2_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (<= (+ (ite (> refinado_3_4 0 ) 1 0 ) (+ (ite (> refinado_3_3 0 ) 1 0 ) (+ (ite (> refinado_3_2 0 ) 1 0 ) (+ (ite (> refinado_3_1 0 ) 1 0 ) (ite (> refinado_3_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (<= (+ (ite (> refinado_4_4 0 ) 1 0 ) (+ (ite (> refinado_4_3 0 ) 1 0 ) (+ (ite (> refinado_4_2 0 ) 1 0 ) (+ (ite (> refinado_4_1 0 ) 1 0 ) (ite (> refinado_4_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (<= (+ (ite (> refinado_5_4 0 ) 1 0 ) (+ (ite (> refinado_5_3 0 ) 1 0 ) (+ (ite (> refinado_5_2 0 ) 1 0 ) (+ (ite (> refinado_5_1 0 ) 1 0 ) (ite (> refinado_5_0 0 ) 1 0 ) ) ) ) ) 3 ) )
(assert-soft (=> (> refinado_0_0 0 ) (>= refinado_0_0 45 ) ) )
(assert-soft (=> (> refinado_0_1 0 ) (>= refinado_0_1 45 ) ) )
(assert-soft (=> (> refinado_0_2 0 ) (>= refinado_0_2 45 ) ) )
(assert-soft (=> (> refinado_0_3 0 ) (>= refinado_0_3 45 ) ) )
(assert-soft (=> (> refinado_0_4 0 ) (>= refinado_0_4 45 ) ) )
(assert-soft (=> (> refinado_1_0 0 ) (>= refinado_1_0 45 ) ) )
(assert-soft (=> (> refinado_1_1 0 ) (>= refinado_1_1 45 ) ) )
(assert-soft (=> (> refinado_1_2 0 ) (>= refinado_1_2 45 ) ) )
(assert-soft (=> (> refinado_1_3 0 ) (>= refinado_1_3 45 ) ) )
(assert-soft (=> (> refinado_1_4 0 ) (>= refinado_1_4 45 ) ) )
(assert-soft (=> (> refinado_2_0 0 ) (>= refinado_2_0 45 ) ) )
(assert-soft (=> (> refinado_2_1 0 ) (>= refinado_2_1 45 ) ) )
(assert-soft (=> (> refinado_2_2 0 ) (>= refinado_2_2 45 ) ) )
(assert-soft (=> (> refinado_2_3 0 ) (>= refinado_2_3 45 ) ) )
(assert-soft (=> (> refinado_2_4 0 ) (>= refinado_2_4 45 ) ) )
(assert-soft (=> (> refinado_3_0 0 ) (>= refinado_3_0 45 ) ) )
(assert-soft (=> (> refinado_3_1 0 ) (>= refinado_3_1 45 ) ) )
(assert-soft (=> (> refinado_3_2 0 ) (>= refinado_3_2 45 ) ) )
(assert-soft (=> (> refinado_3_3 0 ) (>= refinado_3_3 45 ) ) )
(assert-soft (=> (> refinado_3_4 0 ) (>= refinado_3_4 45 ) ) )
(assert-soft (=> (> refinado_4_0 0 ) (>= refinado_4_0 45 ) ) )
(assert-soft (=> (> refinado_4_1 0 ) (>= refinado_4_1 45 ) ) )
(assert-soft (=> (> refinado_4_2 0 ) (>= refinado_4_2 45 ) ) )
(assert-soft (=> (> refinado_4_3 0 ) (>= refinado_4_3 45 ) ) )
(assert-soft (=> (> refinado_4_4 0 ) (>= refinado_4_4 45 ) ) )
(assert-soft (=> (> refinado_5_0 0 ) (>= refinado_5_0 45 ) ) )
(assert-soft (=> (> refinado_5_1 0 ) (>= refinado_5_1 45 ) ) )
(assert-soft (=> (> refinado_5_2 0 ) (>= refinado_5_2 45 ) ) )
(assert-soft (=> (> refinado_5_3 0 ) (>= refinado_5_3 45 ) ) )
(assert-soft (=> (> refinado_5_4 0 ) (>= refinado_5_4 45 ) ) )
(assert-soft (=> (> refinado_0_0 0 ) (> refinado_0_4 0 ) ) )
(assert-soft (=> (> refinado_0_1 0 ) (> refinado_0_4 0 ) ) )
(assert-soft (=> (> refinado_1_0 0 ) (> refinado_1_4 0 ) ) )
(assert-soft (=> (> refinado_1_1 0 ) (> refinado_1_4 0 ) ) )
(assert-soft (=> (> refinado_2_0 0 ) (> refinado_2_4 0 ) ) )
(assert-soft (=> (> refinado_2_1 0 ) (> refinado_2_4 0 ) ) )
(assert-soft (=> (> refinado_3_0 0 ) (> refinado_3_4 0 ) ) )
(assert-soft (=> (> refinado_3_1 0 ) (> refinado_3_4 0 ) ) )
(assert-soft (=> (> refinado_4_0 0 ) (> refinado_4_4 0 ) ) )
(assert-soft (=> (> refinado_4_1 0 ) (> refinado_4_4 0 ) ) )
(assert-soft (=> (> refinado_5_0 0 ) (> refinado_5_4 0 ) ) )
(assert-soft (=> (> refinado_5_1 0 ) (> refinado_5_4 0 ) ) )
(maximize beneficio )
(check-sat)
(get-value (beneficio) )
(get-value (compras_0_0) )
(get-value (compras_0_1) )
(get-value (compras_0_2) )
(get-value (compras_0_3) )
(get-value (compras_0_4) )
(get-value (compras_1_0) )
(get-value (compras_1_1) )
(get-value (compras_1_2) )
(get-value (compras_1_3) )
(get-value (compras_1_4) )
(get-value (compras_2_0) )
(get-value (compras_2_1) )
(get-value (compras_2_2) )
(get-value (compras_2_3) )
(get-value (compras_2_4) )
(get-value (compras_3_0) )
(get-value (compras_3_1) )
(get-value (compras_3_2) )
(get-value (compras_3_3) )
(get-value (compras_3_4) )
(get-value (compras_4_0) )
(get-value (compras_4_1) )
(get-value (compras_4_2) )
(get-value (compras_4_3) )
(get-value (compras_4_4) )
(get-value (compras_5_0) )
(get-value (compras_5_1) )
(get-value (compras_5_2) )
(get-value (compras_5_3) )
(get-value (compras_5_4) )
(get-value (refinado_0_0) )
(get-value (refinado_0_1) )
(get-value (refinado_0_2) )
(get-value (refinado_0_3) )
(get-value (refinado_0_4) )
(get-value (refinado_1_0) )
(get-value (refinado_1_1) )
(get-value (refinado_1_2) )
(get-value (refinado_1_3) )
(get-value (refinado_1_4) )
(get-value (refinado_2_0) )
(get-value (refinado_2_1) )
(get-value (refinado_2_2) )
(get-value (refinado_2_3) )
(get-value (refinado_2_4) )
(get-value (refinado_3_0) )
(get-value (refinado_3_1) )
(get-value (refinado_3_2) )
(get-value (refinado_3_3) )
(get-value (refinado_3_4) )
(get-value (refinado_4_0) )
(get-value (refinado_4_1) )
(get-value (refinado_4_2) )
(get-value (refinado_4_3) )
(get-value (refinado_4_4) )
(get-value (refinado_5_0) )
(get-value (refinado_5_1) )
(get-value (refinado_5_2) )
(get-value (refinado_5_3) )
(get-value (refinado_5_4) )
