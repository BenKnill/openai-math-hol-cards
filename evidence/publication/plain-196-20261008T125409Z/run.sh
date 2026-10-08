#!/usr/bin/env bash
cd /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z
echo "start $(date -u +%Y-%m-%dT%H:%M:%SZ)" > /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.time
echo "HOLDIR=/home/bluestar/hearth/data/hol-light /home/bluestar/scratch/cards-publish-20261008-1255/repo/bin/replay-plain /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/plain-196 196" > /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.cmd
HOLDIR=/home/bluestar/hearth/data/hol-light /home/bluestar/scratch/cards-publish-20261008-1255/repo/bin/replay-plain /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/plain-196 196 > /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.stdout 2> /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.stderr
s=$?
echo $s > /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.exit
echo "end $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> /home/bluestar/scratch/cards-publish-20261008-1255/smoke-196-20261008T125409Z/run.time
exit $s
