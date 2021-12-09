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

(define (to-name f) (regexp-replace #rx".*/([^/]+)/encode_report.xml" f "\\1"))

(define files
  '("./data/data-mining/covariance/encode_report.xml"
    "./data/stencils/heat-3d/encode_report.xml"
    "./data/stencils/jacobi-1d/encode_report.xml"
    "./data/stencils/seidel-2d/encode_report.xml"
    "./data/stencils/jacobi-2d/encode_report.xml"
    "./data/linear-algebra/kernels/doitgen/encode_report.xml"
    "./data/linear-algebra/kernels/2mm/encode_report.xml"
    "./data/linear-algebra/kernels/3mm/encode_report.xml"
    "./data/linear-algebra/blas/gemver/encode_report.xml"
    "./data/linear-algebra/blas/syrk/encode_report.xml"
    "./data/linear-algebra/blas/gemm/encode_report.xml"
    "./data/linear-algebra/solvers/trisolv/encode_report.xml"))

(define (list->hash l)
  (foldr (lambda (v l)
           (hash-set l (car v) (cadr v)))
         (hash) l))

(define (list->hashn l)
  (foldr (lambda (v l)
           (hash-set l (car v) (string->number (cadr v))))
         (hash) l))

(define name-f-map
  (list->hash (map (lambda (f) (list (to-name f) f)) files)))

(define (parse-vivado-report f)
  (let* ([encode-xml-port (open-input-file f)]
         [report (xml->xexpr (document-element (read-xml encode-xml-port)))])
    (close-input-port encode-xml-port)
    report))

(define (process-vivado-report report)
  (let ([maps (map (lambda (x) (match x [(list e (list (list a b) (list c d))) (list b d)]))
                   (filter-not string? (se-path*/list '(section) report)))])
    (list->hashn maps)))

(define (vivado-report-f f) (process-vivado-report (parse-vivado-report f)))

;;(vivado-report-f "./data/data-mining/covariance/encode_report.xml")

(define synth-f (map flatten (hash-map name-f-map
                                       (lambda (n f) (let ([x (vivado-report-f f)])
                                                       (list n
                                                             (hash-ref x "XILINX_LUT_FLIP_FLOP_PAIRS_USED")
                                                             (hash-ref x "XILINX_SLICE")
                                                             (hash-ref x "XILINX_SLICE_REGISTERS")
                                                             (hash-ref x "XILINX_SLICE_LUTS")
                                                             (hash-ref x "XILINX_BLOCK_RAMFIFO")
                                                             (hash-ref x "XILINX_IOPIN")
                                                             (hash-ref x "XILINX_DSPS")
                                                             (hash-ref x "XILINX_POWER")
                                                             (hash-ref x "XILINX_DESIGN_DELAY")))))))

(define (parse-sim-report f)
  (let* ([exec-csv (open-input-file f)]
         [report (csv->list exec-csv)])
    (close-input-port exec-csv)
    report))

(define sim-report (list->hashn (parse-sim-report "exec.csv")))

(define csv (open-output-file "out2.csv"))
(display (table->string
          (append '((benchmark lut_flip_flop slice regs luts ramfifo iopin dsps power delay cycles))
                  (map (lambda (x) (append x (list (hash-ref sim-report (car x))))) synth-f))) csv)
(close-output-port csv)

;;(define vivado-report (process-vivado-report (parse-vivado-report "encode_report.xml")))
;;(define cycles (hash-ref sim-report "covariance"))
;;(define delay (hash-ref vivado-report "XILINX_DESIGN_DELAY"))
;;
;;(define gss (df-read/csv "exec.csv"))
;;
;;(df-add-series gss (make-series "tool" #:data (make-vector (df-row-count gss) "vericert")))
;;
;;(df-add-series gss (make-series "delay" #:data (list->vector (map (lambda (x)
;;                     (~> "/encode_report.xml"
;;                         (string-append x _)
;;                         parse-vivado-report
;;                         process-vivado-report
;;                         (hash-ref "XILINX_DESIGN_DELAY")))
;;                   (filter-not (lambda (x) (equal? x "test-case")) (map car (hash->list sim-report)))))))
;;
;;(show gss everything #:n-rows 'all)
;;
;;(graph #:data gss
;;       #:title "Chart"
;;       #:mapping (aes #:x "test-case" #:y "cycle count")
;;       (col #:gap 0.25))
;;
;;;(define csv (open-output-file "out.csv"))
