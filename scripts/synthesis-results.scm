#! /usr/bin/chicken-csi -s
;; -*- mode: scheme -*-

(import (chicken port)
        (chicken process-context)
        (chicken string)
        (chicken irregex)
        (chicken file)
        args
        matchable
        srfi-193
        ssax)

(define options)
(define operands)

(define (check-opt b) (cdr (or (assoc b options) `(,b . #f))))

(define opts
	(list (args:make-option (v verbose) (optional: "LEVEL") "Debug level [default: 0]"
	                        (set! arg (or arg "0")))
        (args:make-option (k keys) (required: "KEY,KEY,...") "Keys to display [default: slice,ramfifo,delay]")
        (args:make-option (o output) (required: "FILE") "Output file")
        (args:make-option (s suppress) (required: "TYPE,TYPE,...") "Values to suppress from output [default: none]")
        (args:make-option (x xml) #:none "Output raw XML from the synthesis tool")
        (args:make-option (c csv) #:none "Output processed CSV")
	      (args:make-option (V version) #:none "Display version"
	                        (print "synthesise v0.1.0")
	                        (exit))
	      (args:make-option (h help) #:none "Display this text"
	                        (usage))))

(: description string)
(define description
  "synthesis-results: sends a verilog file to be synthesised and returns results as a CSV file.")

(define (usage)
	(with-output-to-port (current-error-port)
	  (lambda ()
      (print description)
      (newline)
	    (print "Usage: " (program-name) " [options...] [files...]")
	    (newline)
	    (print (args:usage opts))
	    (print "Report bugs to git at yannherklotz dot com.")))
  (exit 1))

(define (map-names n)
  (match n
    ["XILINX_LUT_FLIP_FLOP_PAIRS_USED" "lut_flip_flop"]
    ["XILINX_SLICE" "slice"]
    ["XILINX_SLICE_REGISTERS" "regs"]
    ["XILINX_SLICE_LUTS" "luts"]
    ["XILINX_BLOCK_RAMFIFO" "ramfifo"]
    ["XILINX_IOPIN" "iopin"]
    ["XILINX_DSPS" "dsps"]
    ["XILINX_POWER" "power"]
    ["XILINX_DESIGN_DELAY" "delay"]
    [_ n]))

(define (csv:fmt-row l) (string-intersperse (map ->string l) ","))

(define (csv:fmt-table-string l) (apply string-append (map (lambda (s) (string-append s "\n")) l)))

(define (csv:fmt-table l) (apply string-append (map (lambda (s) (string-append s "\n"))
                                                    (map csv:fmt-row l))))

(define (xml-matcher xml)
  (match xml
    [('*TOP* _ ('document ('application ('section _ . r))))
     (map (match-lambda
            [('item ('@ ('value v) ('stringID s))) (list (map-names s) (string->number v))]) r)]))

(define (parse-xml name file)
  (with-input-from-file file
    (lambda ()
      (list name (xml-matcher (ssax:xml->sxml (current-input-port) '()))))))

(define (to-csv-record b head results)
  (let ((res (map (lambda (key)
                    (cadr (assoc key (cadr results)))) head)))
    (csv:fmt-row (if b res (cons (car results) res)))))

(: path-to-name (string -> string))
(define (path-to-name path)
  (irregex-replace "^.*?([^/]+)_report\\.xml$" path 1))

(define (convert-files files)
  (map (lambda (f) (parse-xml (path-to-name f) f)) files))

(: split-at-comma (string -> (list-of string)))
(define (split-at-comma s) (string-split s ","))

(: find-all-xml (string -> (list-of string)))
(define (find-all-xml dir) (find-files dir #:test ".*\\.xml$"))

(define (get-files-from-op operands)
  (match operands
    [(d) (cond [(directory-exists? d) (find-all-xml d)]
               [else (list d)])]
    [_ operands]))

(define (with-output thk)
  (if (check-opt 'output)
      (with-output-to-file (check-opt 'output) thk)
      (thk)))

(define (main args)
  (set!-values (options operands)
	             (args:parse args opts))
  (let ((head (split-at-comma (or (check-opt 'keys) "slice,ramfifo,delay")))
        (suppress (split-at-comma (or (check-opt 'suppress) "none")))
        (files (get-files-from-op operands)))
    (let ((body (map (lambda (f) (to-csv-record (member "name" suppress) head f))
                     (convert-files files)))
          (header (csv:fmt-row (if (member "name" suppress) head (cons "name" head)))))
    (with-output
        (lambda ()
          (display (csv:fmt-table-string
                    (if (member "header" suppress) body (cons header body)))))))))

(main (command-line-arguments))
