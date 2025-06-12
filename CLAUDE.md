# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands
- `lake build` - Build the project
- `lake build BellParts` - Build the main library
- `lake exe lean prover-play/BellParts.lean` - Run a specific Lean file

## Lean Conventions
- Import Mathlib modules in alphabetical order
- Use 2-space indentation, but overall just make sure to use consistent formatting

## Code Style
- Use descriptive names for theorems and lemmas
- Keep proofs modular with helper lemmas
- Include docstrings for important definitions and theorems
