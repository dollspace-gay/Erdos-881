#!/usr/bin/env python3
"""W-alignment calibration probe (Erdős 881 lab).

The final clique escape needs vertices with cofinally many W-aligned
edges: destroyers whose cross-sum u + (m - v) is 2-guarded by u.
Census in random covering toys:
  - bounded-level W-edges (L small) are threshold artifacts: common.
  - grown-level W-edges (L >= SLACK): ~0.4% of vertices, two of them
    at one vertex: ~0.02%.  Rare but non-vacuous at toy scale.
See session notes 2026-07-24 for the inline runs (seeds 7, 17).
"""
