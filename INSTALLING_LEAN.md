# Lean setup (step by step)

Lean's toolchain can feel opaque because three separate pieces work together: **elan** (installer), **Lake** (build tool), and **Mathlib** (a huge dependency). The steps below are the same ones used to set up this project on Linux.

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

## What is in the repo vs. what appears after you build

**Committed (small, human-readable):**

| Path | Purpose |
|------|---------|
| `lean-toolchain` | Pins Lean **4.30.0** (read by [elan](#1-install-elan-lean-version-manager)) |
| `lakefile.toml` | Project config; declares Mathlib **v4.30.0** as a dependency |
| `lake-manifest.json` | Lockfile: exact Git commits for Mathlib and its dependencies |
| `Icon2lean/` | Algorithm implementations (GCD, CRA, FFT, etc.) |
| `Icon2lean.lean` | Root module that imports the library |

**Generated locally (large, gitignored):**

| Path | Purpose | Typical size |
|------|---------|--------------|
| `.lake/packages/` | Downloaded Mathlib and helper libraries | ~7 GB |
| `.lake/build/` | Compiled `.olean` cache for this project | grows with builds |

If you see a multi-gigabyte `.lake/` folder after setup, that is normal. It is intentionally **not** in git.

