#lang racket

(require xml)
(require xml/path)
(require racket/match)

(require csv-reading)
(require csv-writing)

(require graphite)
(require data-frame)
(require sawzall)

(require threading)

(permissive-xexprs #t)

(define (parse-vivado-report f)
  (let* ([encode-xml-port (open-input-file f)]
         [report (xml->xexpr (document-element (read-xml encode-xml-port)))])
    (close-input-port encode-xml-port)
    report))

(define (list->hash l)
  (foldr (lambda (v l)
           (hash-set l (car v) (string->number (cadr v))))
         (hash) l))

(define (process-vivado-report report)
  (let ([maps (map (lambda (x) (match x [(list e (list (list a b) (list c d))) (list b d)]))
                   (filter-not string? (se-path*/list '(section) report)))])
    (list->hash maps)))

(define (parse-sim-report f)
  (let* ([exec-csv (open-input-file f)]
         [report (csv->list exec-csv)])
    (close-input-port exec-csv)
    report))

(define sim-report (list->hash (parse-sim-report "exec.csv")))
(define vivado-report (process-vivado-report (parse-vivado-report "encode_report.xml")))
(define cycles (hash-ref sim-report "covariance"))
(define delay (hash-ref vivado-report "XILINX_DESIGN_DELAY"))

(* cycles delay)

(define gss (df-read/csv "exec.csv"))

(df-add-series gss (make-series "tool" #:data (make-vector (df-row-count gss) "vericert")))

(df-add-series gss (make-series "delay" #:data (list->vector (map (lambda (x)
                     (~> "/encode_report.xml"
                         (string-append x _)
                         parse-vivado-report
                         process-vivado-report
                         (hash-ref "XILINX_DESIGN_DELAY")))
                   (filter-not (lambda (x) (equal? x "test-case")) (map car (hash->list sim-report)))))))

(show gss everything #:n-rows 'all)

(graph #:data gss
       #:title "Chart"
       #:mapping (aes #:x "test-case" #:y "cycle count")
       (col #:gap 0.25))

;(define csv (open-output-file "out.csv"))
