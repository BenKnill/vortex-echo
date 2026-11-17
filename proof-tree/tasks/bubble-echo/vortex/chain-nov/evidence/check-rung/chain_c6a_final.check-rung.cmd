# exact check-rung invocation (bluestar26, 2026-11-13, C6a); output in check-rung-final.out
W=/home/bluestar/lanes/demo1-wave-20261110-141705; B=$W/vortex-chain-20261111-142342
~/lanes/bin/check-rung $B/c6a/runs/20261113T093222Z-1518944-chain_c6a_final-12cd59 --frozen $B/FROZEN-C6A.txt \
  --commit $B/c6a/proj:f1ee50d --commit $B/c3b/proj:a8f41949 --commit $W/vortex-pop/assembly/proj:56b09cf \
  --spec $W/vortex-pop/assembly/proj/tasks/bubble-echo/vortex/proofs/chain_c6a_final.spec \
  --attest $B/c6a/evidence/attest-final.out --runs-root $B/c6a/runs
