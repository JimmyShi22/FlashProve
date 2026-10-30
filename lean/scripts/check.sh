#!/bin/bash
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
# check.sh: the full check of this library. All of it is in check.py beside this file; README.md
# says what each step shows. -I: Python ignores PYTHONPATH and the user's own site directory.
exec python3 -I -B "$(dirname "$(readlink -f "$0")")/check.py" "$@"
