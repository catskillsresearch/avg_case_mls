# Lean setup (step by step)

Lean's toolchain can feel opaque because three separate pieces work together: **elan** (installer), **Lake** (build tool), and **Mathlib** (a huge dependency). The steps below match the setup used for this project on Linux.

## 0. Prerequisites

- **git** — clone this repository  
- **curl** — install elan  
- **Disk space** — allow roughly **10 GB** free for Mathlib + build cache  
- **Time** — first `lake update` and `lake build` can take **10–30+ minutes** depending on CPU and network  

Optional but helpful: [Cursor](https://cursor.com/) or VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

## 1. Install elan (Lean version manager)

[elan](https://github.com/leanprover/elan) is like `rustup` for Rust: it installs Lean and switches versions per project.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

When prompted, accept the default toolchain (you can press Enter). Then load elan into your current shell:

```bash
source "$HOME/.elan/env"
```

To make that permanent, the installer usually adds a line to `~/.bashrc` or `~/.profile`. Open a **new terminal** or run `source ~/.bashrc` before continuing.

Verify:

```bash
elan --version    # e.g. elan 4.2.2
which lake        # should print something like ~/.elan/bin/lake
```

You do **not** need to install Lean manually. elan reads `lean-toolchain` in this repo and downloads **Lean 4.30.0** the first time you run `lake`.

## 2. Clone and enter the project

```bash
git clone https://github.com/catskillsresearch/avg_case_mls.git
cd avg_case_mls
```

## 3. Download dependencies (`lake update`)

Lake is Lean's package manager (similar to `cargo` or `npm`). This step clones Mathlib into `.lake/packages/`:

```bash
lake update
```

What happens:

- Reads `lakefile.toml` → requests Mathlib tag `v4.30.0`  
- Writes/updates `lake-manifest.json` with exact commit hashes  
- Clones several GitHub repos under `.lake/packages/` (Mathlib pulls in batteries, aesop, etc.)

This is the slow, large download. Expect several gigabytes.

## 4. Build the project (`lake build`)

```bash
lake build
```

What happens:

- Compiles Mathlib modules your code imports (incremental; first run is heavy)  
- Typechecks all files under `AvgCaseMls/`  
- Produces cache files under `.lake/build/`  

A successful run ends with something like:

```text
Build completed successfully.
```

## 5. Check the Lean formalization

This repo extracts Lean 4 code from [`arxiv.md`](arxiv.md) (§§2–3 paired with math; §§6–8 for strategy, decision procedures, and hardness). Most theorem proofs are still `sorry`; the current tests focus on definitions that compile and a few decidable examples.

```bash
chmod +x run_lean_check.sh run_lean_tests.sh
./run_lean_check.sh     # typecheck everything
./run_lean_tests.sh     # print #eval smoke-test output
```

Or run the underlying commands directly:

```bash
lake build
lake build AvgCaseMls.Tests 2>&1 | grep "^info: AvgCaseMls/Tests"
```

Expected `#eval` lines include `true`, `false`, `0`, and `3` for the empty-set equality case, inequality case, and bitstring lengths.

## What is in the repo vs. what appears after you build

**Committed (small, human-readable):**

| Path | Purpose |
|------|---------|
| `lean-toolchain` | Pins Lean **4.30.0** (read by [elan](#1-install-elan-lean-version-manager)) |
| `lakefile.toml` | Project config; declares Mathlib **v4.30.0** as a dependency |
| `lake-manifest.json` | Lockfile: exact Git commits for Mathlib and its dependencies |
| `AvgCaseMls/` | MLS embedding, decision-procedure skeleton, AvCom definitions |
| `AvgCaseMls.lean` | Root module that imports the library |
| `run_lean_check.sh` | Runs `lake build` (full typecheck) |
| `run_lean_tests.sh` | Runs `#eval` smoke tests in `AvgCaseMls/Tests.lean` |

**Generated locally (large, gitignored):**

| Path | Purpose | Typical size |
|------|---------|--------------|
| `.lake/packages/` | Downloaded Mathlib and helper libraries | ~7 GB |
| `.lake/build/` | Compiled `.olean` cache for this project | grows with builds |

If you see a multi-gigabyte `.lake/` folder after setup, that is normal. It is intentionally **not** in git.

## Lean library map

| `arxiv.md` section | Module | Status |
|--------------------|--------|--------|
| §2 AvCom (math + Lean encoding) | [`AvgCaseMls/AvCom.lean`](AvgCaseMls/AvCom.lean) | `rank`, `T_inv` still `sorry` |
| §3 MLS (math + Lean encoding) | [`AvgCaseMls/MLS.lean`](AvgCaseMls/MLS.lean) | Phase 2A complete; no `sorry` |
| §6 Lean strategy | (prose in [`arxiv.md`](arxiv.md)) | Roadmap, Mathlib gap, design table |
| §7 Decision procedure | [`AvgCaseMls/DecideMLS.lean`](AvgCaseMls/DecideMLS.lean) | Mock `decideMLS`; proofs are `sorry` |
| §8 Average-case hardness | [`AvgCaseMls/AverageHardness.lean`](AvgCaseMls/AverageHardness.lean) | Theorem statement; proof is `sorry` |
| Smoke tests | [`AvgCaseMls/Tests.lean`](AvgCaseMls/Tests.lean) | `native_decide` / `#eval` on decidable fragments |

## 6. Day-to-day commands

| Command | When to use |
|---------|-------------|
| `./run_lean_check.sh` | After editing `.lean` files — confirms everything still typechecks |
| `./run_lean_tests.sh` | After changing computable definitions — prints `#eval` output |
| `lake build AvgCaseMls` | Build only the library target |
| `lake clean` | Delete `.lake/build/` cache (keeps downloaded packages) |
| `rm -rf .lake && lake update && lake build` | Nuclear reset if dependencies get corrupted |

## Troubleshooting

**`lake: command not found`**  
Run `source "$HOME/.elan/env"` or open a new terminal after installing elan.

**Out of disk space during `lake update`**  
Mathlib needs several GB. Free space or use a machine with more storage; there is no lightweight subset for this project.

**Build runs out of memory**  
Close other apps; Mathlib compilation is RAM-heavy. Retry `lake build` (Lake resumes incrementally).

**Wrong Lean version**  
From the repo root, run `elan toolchain install leanprover/lean4:v4.30.0` then `lake build`. The file `lean-toolchain` should contain `leanprover/lean4:v4.30.0`.

**`.lake/` showed up in `git status`**  
It should be ignored. If git still tracks it, you may have added it before `.gitignore`; run `git rm -r --cached .lake` once (do not delete the folder on disk).

## Reference setup

This Lean layout follows the same pattern as [icon2lean](https://github.com/catskillsresearch/icon2lean): pinned `lean-toolchain`, Mathlib via Lake, a namespaced library under `AvgCaseMls/`, and shell scripts to typecheck and print test output.
