# openai-math-hol-cards
#
#   make check          warm check of every card on the default remote Hearth host (bluestar26), one line per card
#   make check CARDS="158 017"   only those cards
#   make check-local    the same on this machine (needs a local Hearth with the light and heavy profiles)
#   make cold RUN=DIR   cold (Docker) replay of a finished warm run directory; see bin/cold-cards
#   make list           the cards and their profiles
#
# bin/check-remote documents the REMOTE_* variables that point it at another host.

CARDS ?=
STAMP := $(shell date -u +%Y%m%dT%H%M%SZ)

.PHONY: check check-local cold list

check:
	bin/check-remote $(CARDS)

check-local:
	bin/run-cards out/warm-$(STAMP) $(CARDS)

cold:
	@test -n "$(RUN)" || { echo "usage: make cold RUN=<warm run directory containing verdicts.tsv>"; exit 2; }
	bin/cold-cards $(RUN) out/cold-$(STAMP) $(CARDS)

list:
	@awk -F'\t' '!/^#/ {printf "%-10s %-6s %s\n", $$1, $$3, $$6}' cards.tsv
