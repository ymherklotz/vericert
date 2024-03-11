#!/bin/sh
#|
exec csi -ss "$0" "$@"
|#
;; -*- mode: scheme -*-
;;
;; Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

(import (chicken file)
        (chicken io)
        (chicken irregex)
        (chicken port)
        (chicken process-context)
        (chicken sort)
        (chicken string)
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
        (args:make-option (default-sort) #:none "Don't the names of the benchmarks")
        (args:make-option (suppress) (required: "TYPE,TYPE,...") "Values to suppress from output [default: none]")
        (args:make-option (c csv) #:none "Output processed CSV")
        (args:make-option (cycle-file) (required: "FILE") "File which contains the cycle counts for the benchmark")
        (args:make-option (org) #:none "Output processed Org")
        (args:make-option (V version) #:none "Display version"
                          (print "synthesis-results v0.2.0")
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

(define (org:fmt-row l) (string-append "| " (string-intersperse (map ->string l) " | ") " |"))

(define (csv:fmt-table-string l) (apply string-append (map (lambda (s) (string-append s "\n")) l)))

(define (csv:fmt-table l) (apply string-append (map (lambda (s) (string-append s "\n"))
                                                    (map csv:fmt-row l))))

(define (xml-matcher xml)
  (match xml
    [('*TOP* _ ('document ('application ('section _ . r))))
     (map (match-lambda
            [('item ('@ ('value v) ('stringID s))) (cons (map-names s) (string->number v))]) r)]))

(define (parse-xml name file)
  (with-input-from-file file
    (lambda ()
      (cons name (xml-matcher (ssax:xml->sxml (current-input-port) '()))))))

(define (ifn-cons b c l)
  (if b l (cons c l)))

(define ((to-csv-record fmt-row b head) results)
  (let ((res (map (lambda (key)
                    (cdr (assoc key (cadr results)))) head)))
    (fmt-row (ifn-cons b (car results) res))))

(: path-to-name (string -> string))
(define (path-to-name path)
  (irregex-replace "^.*?([^/]+)_report\\.xml$" path 1))

(define (order-data d1 d2)
  (match (list d1 d2)
    [((n1 . _) (n2 . _)) (string<? n1 n2)]))

(define (convert-files sort? files)
  ((if sort? (lambda (l) (sort l order-data)) identity)
   (map (lambda (f) (parse-xml (path-to-name f) f)) files)))

(: split-at-comma (string -> (list-of string)))
(define (split-at-comma s) (string-split s ","))

(define (parse-cycles f)
  (if f (with-input-from-file f
          (lambda () (map (match-lambda [(a b) (cons a b)]) (map split-at-comma (read-lines))))) #f))

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

(define (row-fmt)
  (if (check-opt 'org) org:fmt-row csv:fmt-row))

(define (cycle-file operands)
  (let ((dir (match operands
               [(d) (when (directory-exists? d) d)]
               [_ #f])))
    (or (check-opt 'cycle-file) (if dir (string-append dir "/exec.csv") #f))))

(define (add-cycles data cycles)
  (if cycles
      (map (lambda (f) (list (car f) (cons (cons "cycles" (cdr (assoc (car f) cycles))) (cdr f)))) data)
      data))

(define (main args)
  (set!-values (options operands)
               (args:parse args opts))
  (let ((head (split-at-comma (or (check-opt 'keys) "slice,ramfifo,delay,cycles")))
        (suppress (split-at-comma (or (check-opt 'suppress) "none")))
        (files (get-files-from-op operands)))
    (let ((data (convert-files (not (check-opt 'default-sort)) files))
          (header ((row-fmt) (ifn-cons (member "name" suppress) "name" head)))
          (cycles (parse-cycles (cycle-file operands))))
      (with-output
       (lambda ()
         (display (csv:fmt-table-string
                   (ifn-cons (member "header" suppress) header
                             (map (to-csv-record (row-fmt)
                                                 (member "name" suppress)
                                                 head) (add-cycles data cycles))))))))))
