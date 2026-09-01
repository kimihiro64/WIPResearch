"""Validate the extractable Mathlib candidate module boundary."""

from __future__ import annotations

import re
from collections.abc import Sequence
from typing import Final

MATHLIB_CANDIDATE_COMPONENT: Final[str] = "Mathlib"
MATHLIB_ALLOWED_EXTERNAL_IMPORT_PREFIXES: Final[tuple[str, ...]] = (
    "Batteries.",
    "Init.",
    "Lean.",
    "Mathlib.",
    "Std.",
)
MATHLIB_HEADER_MARKERS: Final[tuple[str, ...]] = (
    "Copyright (c)",
    "Released under Apache 2.0 license",
    "Authors:",
    "/-!",
)
MATHLIB_READINESS_STATES: Final[tuple[str, ...]] = (
    "extracting",
    "project-verified",
    "mathlib-ready",
    "submitted",
    "upstreamed",
)


def is_mathlib_candidate(module: str, namespace: str) -> bool:
    """Return whether a module belongs to the extractable Mathlib layer."""
    root = f"{namespace}.{MATHLIB_CANDIDATE_COMPONENT}"
    return module == root or module.startswith(f"{root}.")


def mathlib_candidate_failures(
    module: str,
    source: str,
    code: str,
    imports: Sequence[str],
    owned_modules: set[str],
    namespace: str,
) -> list[str]:
    """Return violations that would prevent direct extraction toward Mathlib."""
    if not is_mathlib_candidate(module, namespace):
        return []
    failures: list[str] = []
    candidate_root = f"{namespace}.{MATHLIB_CANDIDATE_COMPONENT}"
    if module != candidate_root:
        for marker in MATHLIB_HEADER_MARKERS:
            if marker not in source:
                failures.append(f"{module}: Mathlib candidate missing source marker {marker!r}")
    for dependency in imports:
        if dependency in owned_modules:
            if not is_mathlib_candidate(dependency, namespace):
                failures.append(f"{module}: Mathlib candidate imports project module {dependency}")
        elif not dependency.startswith(MATHLIB_ALLOWED_EXTERNAL_IMPORT_PREFIXES):
            failures.append(
                f"{module}: Mathlib candidate imports non-Mathlib dependency {dependency}"
            )
    body = "\n".join(line for line in code.splitlines() if not line.lstrip().startswith("import "))
    if re.search(rf"\b{re.escape(namespace)}\b", body):
        failures.append(
            f"{module}: Mathlib candidate body references project namespace {namespace}"
        )
    return failures


def mathlib_manifest_failures(
    candidate_modules: Sequence[str], namespace: str, manifest: str
) -> list[str]:
    """Require one destination/readiness row for every real candidate module."""
    candidate_root = f"{namespace}.{MATHLIB_CANDIDATE_COMPONENT}"
    failures: list[str] = []
    for module in candidate_modules:
        if module == candidate_root:
            continue
        rows = [line for line in manifest.splitlines() if f"`{module}`" in line]
        if len(rows) != 1:
            failures.append(f"{module}: expected exactly one MATHLIB_PORTING.md inventory row")
            continue
        row = rows[0]
        if "`Mathlib/" not in row:
            failures.append(f"{module}: inventory row lacks a proposed Mathlib path")
        if not any(state in row for state in MATHLIB_READINESS_STATES):
            failures.append(f"{module}: inventory row lacks a recognized readiness state")
    return failures
