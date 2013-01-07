#!/bin/bash

filename=$1'.tex'

cat head.templ > $filename
gtl -m tikz '../'$1'.gtl' >> $filename
cat tail.templ >> $filename

#pdflatex $filename

#evince simple.pdf
