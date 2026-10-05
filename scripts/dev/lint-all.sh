#!/usr/bin/env bash


echo "Running linter for Lean files"

./scripts/lint/required/lint-style.sh

echo "Building Physlib"

lake build Physlib

echo "Run linter"

lake exe runLinter Physlib

echo "Run shake"

lake exe shake Physlib
