# avg_cas_mls

Revisit a 1995 paper on average case complexity of multilevel syllogistic (Courant Institute technical report CS-TR #711).
Recap the ideas of the day and how they have translated into the present
The source report is [`TR1995-711.pdf`](TR1995-711.pdf); the paper-style treatment is [`arxiv.md`](arxiv.md).
The goals of this paper are:
* Topic of original paper (marrying average case complexity to decision procedures for MLS) - call this AvCom
* Recap MLS and its decision procedures
* Recap the average case complexity as of the time of the paper (1995) including "the nose" and any visualizations presented in the original paper and present all of the AvCom classes currently distinguished and results on those classes
* Whether this paper was ever referred to and whether the specific application of AvCom to MLS was ever pursued
* Subsequent development and applications of AvCom to date (2026)
* Formalize MLS in Lean 4
* Code the decision procedures for MLS in Lean 4
* Code the AvCom complexity analysis in Lean 4
* The original paper is pasted earlier in the chat.
* Use Lean 4 to prove that the decision procedures lie in a certain AvCom class as originally stated in the 1995 paper
* Suggestions for future work

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

---

## Lean setup (step by step)

Lean's toolchain can feel opaque because three separate pieces work together: **elan** (installer), **Lake** (build tool), and **Mathlib** (a huge dependency). The steps below are the same ones used to set up this project on Linux.

### 0. Prerequisites

- **git** — clone this repository  
- **curl** — install elan  
- **Disk space** — allow roughly **10 GB** free for Mathlib + build cache  
- **Time** — first `lake update` and `lake build` can take **10–30+ minutes** depending on CPU and network  

Optional but helpful: [Cursor](https://cursor.com/) or VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

### 1. Install elan (Lean version manager)

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

### 2. Clone and enter the project

```bash
git clone https://github.com/catskillsresearch/avg_case_mls.git
cd icon2lean
```


### 3. Download dependencies (`lake update`)

Lake is Lean's package manager (similar to `cargo` or `npm`). This step clones Mathlib into `.lake/packages/`:

```bash
lake update
```

What happens:

- Reads `lakefile.toml` → requests Mathlib tag `v4.30.0`  
- Writes/updates `lake-manifest.json` with exact commit hashes  
- Clones several GitHub repos under `.lake/packages/` (Mathlib pulls in batteries, aesop, etc.)

This is the slow, large download. Expect several gigabytes.

### 4. Build the project (`lake build`)

```bash
lake build
```

What happens:

- Compiles Mathlib modules your code imports (incremental; first run is heavy)  
- Produces cache files under `.lake/build/`  


## Optional: regenerate the markdown from the PDF

The PDF→markdown script uses only Python stdlib plus system **mutool** (MuPDF):

```bash
# Debian/Ubuntu
sudo apt install mupdf-tools

mutool convert -F txt -o /tmp/mutool_full.txt Courant_Ericson_1986.pdf
python3 scripts/pdf_to_md.py /tmp/mutool_full.txt Courant_Ericson_1986.md
```

No Poetry or virtualenv is required unless you add Python dependencies later.

---

## Contributions and Collaboration

This repository functions strictly as a unilateral broadcast of public code for educational and research purposes.

* **Pull Requests and Issues:** This project does not accept external Pull Requests, code contributions, or modifications, and tracking features have been disabled. Any external collaboration vectors are closed.
* **Forks:** Users are entirely free and encouraged to fork or clone this repository to modify the code on their own profiles in accordance with the repository's Apache 2.0 License.

## Regulatory and Liability Disclaimer

* **Limitations:** The code provided herein is for theoretical research and academic simulation purposes only.
* **Liability Protection:** In accordance with Section 8 of the Apache 2.0 License, this software is provided "AS IS" without warranties of any kind. Catskills Research Company disclaims all liability for any direct, indirect, or consequential damages resulting from the use, misuse, or deployment of this simulation code.
