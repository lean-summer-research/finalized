# Finalized Lean Project

**Blueprint**: [lean-summer-research.github.io/finalized/](https://lean-summer-research.github.io/finalized/)

## Guides and Resources (in the Resources folder)

- **[BlueprintGuide.md](Resources/BlueprintGuide.md)** 
- **[NamingConventions.md](Resources/NamingConventions.md)** 
- **[CodeFormatting.md](Resources/CodeFormatting.md)** 
- **[DocumentationStandards.md](Resources/DocumentationStardards.md)**
- **[BestPractices.md](Resources/BestPractices.md)** 

## Project Structure

### MyProject/ - Main Lean Code

```
MyProject/
├── Idempotent.lean          # Idempotent elements in finite semigroups
├── PNatPow.lean             # Positive natural number exponentiation for semigroups  
└── Green/
    ├── Defs.lean            # Definitions of Green's relations (𝓡, 𝓛, 𝓙, 𝓗, 𝓓)
    ├── Basic.lean           # Basic idempotent properties and morphism preservation
    └── Finite.lean          # Properties specific to finite semigroups (𝓓-𝓙 Theorem)
```

### WorkInProgress/ - Unfinished Lean Code

```
WorkInProgress/
├── Ideals.lean
└── Substructures.lean
```

Files in this directory cannot be imported by other files since they're outside the main `MyProject/` directory, but they can freely import from both `MyProject/` and Mathlib. Once a file in this folder is completed, it can be moved into `MyProject/` to be built with the rest of the project.

### LaTeX/ - Blueprint Documentation

```
LaTeX/
├── Chapters.tex              # Main file including all other LaTeX files
├── Idempotent.tex           # Documentation for Idempotent.lean
└── Green/
    ├── Basic.tex            # Documentation for Green/Basic.lean
    ├── Defs.tex            # Documentation for Green/Defs.lean
    └── Finite.tex          # Documentation for Green/Finite.lean
```

## Installing Dependencies

### Option 1: GitHub Codespace (Recommended)

The easiest way to start working with this project is using GitHub Codespaces:

1. Open the green "Code" button, go to the "Codespaces" tab, and choose "Create codespace on main."

2. Wait for the setup to finish. The codespace will automatically configure the Lean environment and also install the LeanBlueprint and LaTeX/latexmk dependencies needed to build the blueprint.

3. Start coding in the browser with a fully configured Lean setup.

After creating the codespace, you can come back to it later without waiting for it to rebuild — just click the green "Code" button again and it will appear under the "Codespaces" tab.

### Option 2: Local Development with Dev Container

This project includes a **dev container** - a containerized development environment that ensures consistent setup across different machines.

**To use the dev container locally:**
1. Install [Docker](https://www.docker.com/get-started)
2. Install the [Dev Containers extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
3. Clone this repository: `git clone https://github.com/lean-summer-research/finalized.git`
4. Open the project in VS Code
5. When prompted, click "Reopen in Container" (or use Ctrl/Cmd+Shift+P → "Dev Containers: Reopen in Container")

### What the Dev Container (and Codespace) Provides

Our dev container automatically sets up:
- Lean 4 with the correct toolchain version
- Mathlib dependencies
- VS Code Lean extension
- leanblueprint tool and LaTeX dependencies for local blueprint compilation
