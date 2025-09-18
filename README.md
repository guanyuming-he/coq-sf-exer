# What is this repo?
It contains my solutions for the books of Software Foundations
(https://softwarefoundations.cis.upenn.edu/) 

## Difference from the Official	files
To split things with a finer granularity and impose a structure among the
files, I arrange each chapter into a unique directory and split long files into
shorter ones. As such, they are incompatible with the official marking
procedure. I also removed some non-exercise content, as the repo mainly serves
as a collection of exercise solutions.

## Progress
Volume 1 (LF), Chapter 17 (AltAuto)

# Compilation?
For volume `X`,
```
cd ./volX
rocq makefile -f ./_CoqProject
make -f ./CoqMakefile
```
See https://rocq-prover.org/doc/V9.0.0/refman/practical-tools/utilities.html#

