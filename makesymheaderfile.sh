#!/bin/sh
genius homogpowers-sym.gel | sed 's/^ /{/' | sed 's/^\[/{/' | sed 's/\([0-9]\)$/\1},/' | sed 's/\]$/}};/'
