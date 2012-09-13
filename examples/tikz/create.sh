#!/bin/bash

filename='simple.tex'
gtl_dir='/home/tuwibs/projects/gtl/'

cat head.templ > $filename
gtl -m tikz $gtl_dir'examples/'$1 >> $filename
cat tail.templ >> $filename

#pdflatex $filename

#evince simple.pdf
