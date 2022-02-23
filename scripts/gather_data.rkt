#lang racket

(require racket/match)
(require racket/list)
(require racket/file)

(require threading)

(require xml)
(require xml/path)

(require csv-reading)
(require csv-writing)

(require graphite)
(require data-frame)
(require sawzall)

(permissive-xexprs #t)

(define (to-name f) (regexp-replace #rx".*/([^/]+)" f "\\1"))

(define (write-file file data)
  (with-output-to-file file
    (lambda ()
      (display data))
    #:exists 'replace))

(define files (file->lines "../benchmarks/polybench-syn/benchmark-list-master"))
(define base "/home/ymherklotz/projects/mpardalos-vericert/results-vericert-fun-full-inlining")

(define (list->hash l)
  (foldr (lambda (v l)
           (hash-set l (car v) (cadr v)))
         (hash) l))

(define (list->hashn l)
  (foldr (lambda (v l)
           (hash-set l (car v) (string->number (cadr v))))
         (hash) l))

(define name-f-map
  (list->hash (map (lambda (f) (list (to-name f) (string-append base "/" f "_report.xml"))) files)))

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
;;
;;(vivado-report-f "/home/ymherklotz/projects/mpardalos-vericert/results-vericert-fun-full-inlining/medley/nussinov_report.xml")

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

(define sim-report (list->hashn (parse-sim-report (string-append base "/exec.csv"))))

(write-file "out.csv"
 (table->string
  (append '((benchmark lut_flip_flop slice regs luts ramfifo iopin dsps power delay cycles))
          (map (lambda (x) (append x (list (hash-ref sim-report (car x))))) synth-f))))

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
