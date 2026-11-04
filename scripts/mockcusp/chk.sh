#!/bin/bash
# compile one Lean file, print errors, and exit status
cd ~/RamanujanTau
export OMP_NUM_THREADS=2
nice -n 10 lake env lean "$1" > /private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/mockcusp_out.txt 2>&1
s=$?
grep -v "^warning\|linter\|^Note" /private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/mockcusp_out.txt | head -${2:-60}
echo "EXIT $s"
