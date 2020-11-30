(deftemplate cell
 (slot x (type INTEGER) (range 0 ?VARIABLE))
 (slot y (type INTEGER) (range 0 ?VARIABLE))
 (slot val (type INTEGER) (default -1))
 (slot rev (type SYMBOL) (default false) (allowed-values true false))
 (slot vis (type SYMBOL) (default false) (allowed-values true false))
)

(deftemplate gcell
    (slot x (type INTEGER) (range 0 ?VARIABLE))
    (slot y (type INTEGER) (range 0 ?VARIABLE)) 
    (slot val (type INTEGER) (default 0))
)

(deftemplate bombpos
  (slot x (type INTEGER) (range 0 ?VARIABLE))
  (slot y (type INTEGER) (range 0 ?VARIABLE))
)

(deftemplate player (slot x)(slot y))
(deftemplate to-move (slot arah))
(deftemplate to-check (slot d))
(deftemplate to-rev (slot d))
(deftemplate to-next (slot d))
(deftemplate to-rmcheck (slot d))
(deftemplate ncheck (slot x)(slot y)(slot val)(slot checked))

(defglobal
    ?*pstat* = 0
    ?*pbomb* = 0
    ?*c-0* = 1
)

(deffacts PlayerInit
  (player (x 0)(y 0))
  (to-check (d 1))
)

(defrule Initialize
  (declare (salience 100))
  =>
  (printout t "Enter board size (min 4 max 10) : ")
  (bind ?size (read))
  (if (< ?size 4)
    then
      (bind ?size 4)
  )
  (if (> ?size 10)
    then
      (bind ?size 10)
  )
  (assert (boardSize ?size))
  (loop-for-count (?r 0 (- ?size 1)) 
    (loop-for-count (?c 0 (- ?size 1)) 
      (if (and (eq ?r 0) (eq ?c 0))
        then
          (assert
            (cell 
              (x ?r) (y ?c) (val 0) (rev true)
            )
          )
        else
          (assert (cell (x ?r) (y ?c)))
      )
      (assert (gcell (x ?r) (y ?c)))
    )
  )
  (assert (BoardCreated))
)

(defrule PutBombs
  (declare (salience 100))
  ?temp <- (BoardCreated)
  (boardSize ?size)
  =>
  (retract ?temp)
  (printout t "Enter amount of bombs : ")
  (bind ?count (read))
  (if (> ?count (* ?size ?size)) 
    then
      (printout t "Jumlah bom melebihi kotak permainan!" crlf)
      (assert (BoardCreated))
    else
      (printout t "(Row and column number starts from 0)" crlf)
      (loop-for-count ?count
          (printout t "Enter bomb x coordinate : ")
          (bind ?x (read))
          (printout t "Enter bomb y coordinate : ")
          (bind ?y (read))
          (assert 
            (bombpos 
              (x ?x) 
              (y ?y)
            )
          )
      ) 
  )
)

(defrule AddValue
  (declare (salience 100))
  (bombpos (x ?x) (y ?y))
  (boardSize ?size)
  =>
  (loop-for-count (?c1 0 8)
    (loop-for-count (?c2 0 8)
      (bind ?curX (+ (- ?x 1) (mod ?c1 3)))
      (bind ?curY (+ (- ?y 1) (mod ?c2 3)))
      (if (and (and (>= ?curX 0) (< ?curX ?size)) (and (>= ?curY 0) (< ?curY ?size))) 
        then
          (if (or (neq ?curX ?x) (neq ?curY ?y))
            then
              (assert (addValueReq ?curX ?curY))
            else
              (assert (bombSpecialValueReq ?curX ?curY))
          )
      )
    )
  )
)

(defrule AddValueRes
  (declare (salience 100))
  ?req <- (addValueReq ?x ?y)
  ?cell <- (gcell (x ?x) (y ?y) (val ?val))
  =>
  (modify ?cell (val (+ ?val 1)))
  (retract ?req)
)

(defrule BombSpecialValueRes
  (declare (salience 90))
  ?req <- (bombSpecialValueReq ?x ?y)
  ?cell <- (gcell (x ?x) (y ?y) (val ?val))
  =>
  (modify ?cell (val 9))
  (retract ?req)
)

(defrule move-right 
?player <- (player (x ?x)(y ?y))
?move <- (to-move(arah right))
 =>
(retract ?player ?move)
(assert (player (x ?x)(y (+ ?y 1))))
)

(defrule move-left
?player <- (player (x ?x)(y ?y))
?move <- (to-move(arah left))
 =>
(retract ?player ?move)
(assert (player (x ?x)(y (- ?y 1))))
)

(defrule move-up
?player <- (player (x ?x)(y ?y))
?move <- (to-move(arah up))
 =>
(retract ?player ?move)
(assert (player (x (+ ?x 1))(y ?y)))
)

(defrule move-down
?player <- (player (x ?x)(y ?y))
?move <- (to-move(arah up))
 =>
(retract ?player ?move)
(assert (player (x (- ?x 1))(y ?y)))
)

(defrule eval-surrounding
    (declare (salience 30))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(rev true))
    (cell (x ?cx)(y ?cy)(val ?v)(rev ?r)(vis false))
    ?nch <- (ncheck (x ?cx)(y ?cy)(checked ~true))
    ?chk <- (to-check (d 1))
    (test 
        (and
            (<= ?cx (+ ?px 1)) (>= ?cx (- ?px 1))
            (<= ?cy (+ ?py 1)) (>= ?cy (- ?py 1))
            (not(and (eq ?cx ?px) (eq ?cy ?py)))
        )
    )
=>  
    (if (>= ?v 9)
        then
        (bind ?*pbomb* (+ ?*pbomb* 1))
    )
    (if (eq ?r false)
        then
        (bind ?*pstat* (+ ?*pstat* 1))
    ;;;    (printout t "========>" ?cx ", " ?cy " not revealed" crlf)
    )    
    (retract ?nch)
    (assert (ncheck (x ?cx)(y ?cy)(checked true)))
)

(defrule check-surrounding
    (declare (salience 31))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(rev true))
    (cell (x ?cx)(y ?cy)(val ?v)(rev ?r)(vis false))
    ?chk <- (to-check (d 1))
    (test 
        (and
            (<= ?cx (+ ?px 1)) (>= ?cx (- ?px 1))
            (<= ?cy (+ ?py 1)) (>= ?cy (- ?py 1))
            (not(and (eq ?cx ?px) (eq ?cy ?py)))
        )
    )
=>
    (assert (ncheck (x ?cx)(y ?cy)(checked false)))
)

(defrule elim-check
    (declare (salience 29))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv)(rev ?pr))
    ?chk <- (to-check (d 1))
    ?cel <- (cell (x ?px)(y ?py)(val ?v)(rev ?r))
    ?nch <- (ncheck (x ?x)(y ?y))
=>
    (retract ?chk ?cel)
;;;    (printout t "pstat: " ?*pstat* " | pv: " ?pv " | pbomb: " ?*pbomb* crlf)
    (if (and (eq ?*pstat* 4) (eq ?pv 4))
        then
        (assert (to-rev (d 4)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 4) (eq ?pv 3))
        then
        (assert (to-rev (d 2)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 4) (eq ?pv 2))
        then
        (assert (to-rev (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 4) (eq ?pv 1))
        then
        (assert (to-rev (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 1) (eq ?pv 4))
        then
        (retract ?nch)
        (assert (to-rev (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 0) (eq ?pv 4))
        then
        (retract ?nch)
        (assert (to-next (d 4)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )

    (if (and (eq ?*pstat* 3) (eq ?pv 3))
        then
        (assert (to-rev (d 3)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 3) (eq ?pv 2) (eq ?*pbomb* 2))
        then
        (assert (to-rev (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
    ;;;    (printout t "============CAN REVEAL=============" crlf)
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 3) (eq ?pv 2))
        then
        (assert (to-rev (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 3) (eq ?pv 1))
        then
        (assert (to-rev (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 0) (eq ?pv 3))
        then
        (retract ?nch)
        (assert (to-next (d 3)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )

    (if (and (eq ?*pstat* 2) (eq ?pv 2))
        then
        (assert (to-rev (d 2)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
    ;;;    (printout t "==========Next 1 cell============" crlf)
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 1) (eq ?pv 2))
        then
        (retract ?nch)
        (assert (to-next (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 0) (eq ?pv 2) (eq ?*pbomb* 2))
        then
        (assert (to-rev (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
    ;;;    (printout t "============CAN REVEAL=============" crlf)
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 0) (eq ?pv 2))
        then
        (retract ?nch)
        (assert (to-next (d 2)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 1) (eq ?pv 2))
        then
        (retract ?nch)
        (assert (to-next (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )

    (if (and (eq ?*pstat* 1) (eq ?pv 1))
        then
        (assert (to-rev (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (eq ?*pstat* 0) (eq ?pv 1))
        then
        (retract ?nch)
        (assert (to-next (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    ;;;    (printout t "Next 1 cell" crlf)
    )

    (if (and (eq ?*pstat* 0) (eq ?pv 0))
        then
        (retract ?nch)
        (assert (to-next (d 1)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
    )
    (if (and (neq ?*pstat* 0) (eq ?pv 0))
        then
        (assert (to-rev (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
        (bind ?*c-0* (- ?*c-0* 1))
    )
    (if (eq ?pv 0)
        then
        (retract ?nch)
        (assert (to-next (d 0)))
        (assert (cell (x ?px)(y ?py)(val ?pv)(rev ?pr)(vis true)))
        (bind ?*pstat* 0)
        (bind ?*pbomb* 0)
        (bind ?*c-0* (- ?*c-0* 1))
    )
)


(defrule reveal-next-0
    (declare (salience 20))
    (to-rev (d 0))
    ?n <- (ncheck (x ?x)(y ?y))
    ?c <- (cell (x ?x)(y ?y)(val -1)(rev false))
    ?g <- (gcell (x ?x)(y ?y)(val ?gv))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?c ?n)
    (assert (cell (x ?x)(y ?y)(val ?gv)(rev true)(vis false)))
    (printout t "Revealing " ?x ", " ?y " as " ?gv crlf)
    (if (eq ?gv 0)
        then
        (bind ?*c-0* (+ ?*c-0* 1))
    )
    (if (eq ?pv 1)
        then
        (assert (to-next (d 1)))    
    )
)

(defrule reveal-next-1
    (declare (salience 20))
    (to-rev (d 1))
    ?n <- (ncheck (x ?x)(y ?y))
    ?c <- (cell (x ?x)(y ?y)(rev false))
    ?g <- (gcell (x ?x)(y ?y)(val ?gv))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?c ?n)
    (assert (cell (x ?x)(y ?y)(val 9)(rev true)(vis false))
            (to-next (d 1)))
    (if (eq ?pv 1)
        then
        (assert (to-next (d 1)))    
    )
    (printout t "Revealing " ?x ", " ?y " as " ?gv  crlf)
)

(defrule reveal-next-2
    (declare (salience 20))
    (to-rev (d 2))
    ?n <- (ncheck (x ?x)(y ?y))
    ?c <- (cell (x ?x)(y ?y)(rev false))
    ?g <- (gcell (x ?x)(y ?y)(val ?gv))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?c ?n)
    (assert (cell (x ?x)(y ?y)(val 9)(rev true)(vis false))
            (to-next (d 1)))
    (if (eq ?pv 1)
        then
        (assert (to-next (d 2)))    
    )
    (printout t "Revealing " ?x ", " ?y " as " ?gv  crlf)
)

(defrule reveal-next-3
    (declare (salience 20))
    (to-rev (d 3))
    ?n <- (ncheck (x ?x)(y ?y))
    ?c <- (cell (x ?x)(y ?y)(rev false))
    ?g <- (gcell (x ?x)(y ?y)(val ?gv))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?c ?n)
    (assert (cell (x ?x)(y ?y)(val 9)(rev true)(vis false))
            (to-next (d 2)))
    (if (eq ?pv 2)
        then
        (assert (to-next (d 3)))    
    )
    (printout t "Revealing " ?x ", " ?y " as " ?gv  crlf)
)

(defrule reveal-next-4
    (declare (salience 20))
    (to-rev (d 4))
    ?n <- (ncheck (x ?x)(y ?y))
    ?c <- (cell (x ?x)(y ?y)(rev false))
    ?g <- (gcell (x ?x)(y ?y)(val ?gv))
    (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?c ?n)
    (assert (cell (x ?x)(y ?y)(val 9)(rev true)(vis false))
            (to-next (d 3)))
    (if (eq ?pv 3)
        then
        (assert (to-next (d 4)))    
    )
    (printout t "Revealing " ?x ", " ?y " as " ?gv  crlf)
)


(defrule move-to-next-0
    (declare (salience 5))
    ?r <- (to-next (d ?))
    ?c <- (cell (x ?x)(y ?y)(val 0)(rev true)(vis false))
    ?p <- (player (x ?px)(y ?py))
    (cell (x ?px)(y ?py)(val ?pv))
=>
    (retract ?p ?r ?c)
    (assert (player (x ?x)(y ?y)) (to-check (d 1))
            (cell (x ?x)(y ?y)(val 0)(rev true)(vis true)))
    (printout t "Moving to " ?x ", " ?y crlf)
    (bind ?*pstat* 0)
	(assert (printBoardFact 1))
)

(defrule move-to-next-1
    (declare (salience 4))
    ?r <- (to-next (d 0|1))
    (cell (x ?x)(y ?y)(val 1)(rev true)(vis false))
    ?p <- (player (x ?px)(y ?py))
=>
    (retract ?p ?r)
    (assert (player (x ?x)(y ?y)) (to-check (d 1))
            (cell (x ?x)(y ?y)(val 1)(rev true)(vis true)))
    (printout t "Moving to " ?x ", " ?y crlf)
    (bind ?*pstat* 0)
	(assert (printBoardFact 1))
)

(defrule move-to-next-2
(declare (salience 3))
    ?r <- (to-next (d 1|2))
    (cell (x ?x)(y ?y)(val 2)(rev true)(vis false))
    ?p <- (player (x ?px)(y ?py))
=>
    (retract ?p ?r)
    (assert (player (x ?x)(y ?y)) (to-check (d 1))
            (cell (x ?x)(y ?y)(val 2)(rev true)(vis true)))
    (printout t "Moving to " ?x ", " ?y crlf)
    (bind ?*pstat* 0)
	(assert (printBoardFact 1))
)

(defrule move-to-next-3
(declare (salience 2))
    ?r <- (to-next (d 2|3))
    (cell (x ?x)(y ?y)(val 3)(rev true)(vis false))
    ?p <- (player (x ?px)(y ?py))
=>
    (retract ?p ?r)
    (assert (player (x ?x)(y ?y)) (to-check (d 1))
            (cell (x ?x)(y ?y)(val 3)(rev true)(vis true)))
    (printout t "Moving to " ?x ", " ?y crlf)
    (bind ?*pstat* 0)
	(assert (printBoardFact 1))
)

(defrule move-to-next-4
(declare (salience 1))
    ?r <- (to-next (d 3|4))
    (cell (x ?x)(y ?y)(val 4)(rev true)(vis false))
    ?p <- (player (x ?px)(y ?py))
=>
    (retract ?p ?r)
    (assert (player (x ?x)(y ?y)) (to-check (d 1))
            (cell (x ?x)(y ?y)(val 4)(rev true)(vis true)))
    (printout t "Moving to " ?x ", " ?y crlf)
    (bind ?*pstat* 0)
	(assert (printBoardFact 1))
)

(defrule retract-ncheck
    (declare (salience 80))
    (to-rmcheck (d 1))
    ?n <- (ncheck (x ?)(y ?))
    =>
    (retract ?n)
)

(defrule stop-retract-ncheck
    (declare (salience 70))
    ?n <- (to-rmcheck (d 1))
    =>
    (retract ?n)
)

(defrule startprintingbombs
  (declare (salience -90))
  =>
  (printout t "Here are the locations of bombs found (x, y):" crlf)
  (assert (initLastBoard 1))
)

(defrule printbombs
  (declare (salience -100))
  (cell (x ?x) (y ?y) (val 9) (rev true) (vis ?))
  =>
  (printout t "(" ?x ", " ?y ")" crlf)
)

;;;
;;; Matrix printer
;;;

(defrule initLastPrintBoard
	(declare (salience -999))
	?ilbf <- (initLastBoard ?data)
	=>
	(retract ?ilbf)
	(printout t "The fully revealed board is as follows:" crlf)
	(assert (printBoardFact 1))
)


(defrule printBoard
  (declare (salience 129))
  (printBoardFact ?data)
  (boardSize ?size)
  =>
    (printout t "==")
	(loop-for-count (?x 0 (- ?size 1))  
      (printout t "==="))
    (printout t crlf)
	(printout t "==")
	(loop-for-count (?x 0 (- ?size 1))  
      (printout t "=" ?x "="))
    (printout t crlf)
	(printout t "+-")
    (loop-for-count (?x 0 (- ?size 1))  
      (printout t "+-+"))
     (printout t crlf)
	
	(assert (printRowNum 0))
    (assert (printX 0))
    (assert (printY 0))
)

(defrule printRowNum
	(declare (salience 136))
	?prnf <- (printRowNum ?prn)
	=>
	(printout t ?prn ">")
	(retract ?prnf))

(defrule printBoardCell
  (declare (salience 130))
  ?prxf <- (printX ?prx)
  ?pryf <- (printY ?pry)
  (cell (x ?prx)(y ?pry)(val ?pv))
  =>  
  (bind ?char "+")
  (if (eq ?pv -1)
    then
      (bind ?char " ")
  )
  (if (eq ?pv 9)
        then
        (bind ?char "x")    
    )
  (if (eq ?char "+")
    then
    (bind ?char ?pv)
  )
  (printout t "|" ) (printout t ?char) (printout t "|")
  (retract ?prxf)
  (assert (printX (+ ?prx 1)))
)

(defrule printBoardNextY
  (declare (salience 129))
  ?prxf <- (printX ?prx)
  ?pryf <- (printY ?pry)
  (boardSize ?size)
  (test (eq ?size ?prx))
  =>
  (retract ?prxf ?pryf)
  (assert (printX 0))
  (assert (printY (+ ?pry 1)))
  (assert (printRowNum (+ ?pry 1)))
  (printout t crlf)
)

(defrule printBoardStop
  (declare (salience 149))
  ?prxf <- (printX ?prx)
  ?pryf <- (printY ?pry)
  (boardSize ?size)
  (test (eq ?size ?pry))
  ?pbf <- (printBoardFact ?data)
  ?prnf <- (printRowNum ?prn)
  =>
  (retract ?prxf ?pryf ?pbf ?prnf)
  (printout t "+-")
  (loop-for-count (?x 0 (- ?size 1))  
    (printout t "+-+"))
   (printout t crlf)
   (printout t "~~")
   (loop-for-count (?x 0 (- ?size 1))  
    (printout t "~~~"))
  (printout t crlf)
  (printout t crlf)
)