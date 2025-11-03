# Finalized Lean Project

This repository contains a Lean 4 formalization project focused on semigroup theory, Green's relations, and idempotent elements. The project includes comprehensive documentation, style guidelines, and an interactive mathematical blueprint.

## Resources and Documentation

We maintain comprehensive documentation in the `Resources/` folder:

### Style and Coding Guidelines

- **[NamingConventions.md](Resources/NamingConventions.md)** - Complete guide to Lean naming conventions with examples from our codebase
- **[CodeFormatting.md](Resources/CodeFormatting.md)** - Formatting rules for Lean code (line length, tactics, operators)
- **[DocumentationStandards.md](Resources/DocumentationStardards.md)** - Standards for docstrings, comments, and file structure
- **[BestPractices.md](Resources/BestPractices.md)** - High-level coding practices and quick reference

### Blueprint Documentation

- **[BlueprintGuide.md](Resources/BlueprintGuide.md)** - Complete guide to editing and using the Lean Blueprint system

**New contributors should read these files to understand our conventions and workflows.**

## Quick Links

- **Interactive Blueprint**: [lean-summer-research.github.io/finalized/](https://lean-summer-research.github.io/finalized/)
- **API Documentation**: Available through the blueprint website
- **Dependency Graph**: Visual representation of theorem dependencies in the blueprint

## Table of Contents

- [Getting Started](#getting-started)
- [Project Structure](#project-structure)
- [Development Environment](#development-environment)
- [Interactive Blueprint](#interactive-blueprint)
- [Contributing](#contributing)

## Getting Started

### Option 1: GitHub Codespace (Recommended)

The easiest way to start working with this project is using GitHub Codespaces:

1. **Open in Codespace**: Click the green "Code" button → "Codespaces" tab → "Create codespace on main"
2. **Wait for setup**: The codespace will automatically configure the Lean environment (this may take a few minutes)
3. **Start coding**: Once loaded, you'll have a fully configured Lean development environment with VS Code in your browser

### Option 2: Local Development with Dev Container

This project includes a **dev container** - a containerized development environment that ensures consistent setup across different machines.

**What is a dev container?**
A dev container is a Docker-based development environment that includes all necessary tools, extensions, and dependencies pre-configured. It ensures that everyone working on the project has an identical development setup.

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

The `WorkInProgress/` folder contains Lean files that are still under development and serves as an experimental workspace for new ideas and partial proofs. Files in this directory have a unique property: they cannot be imported by other files since they're outside the main `MyProject/` directory, but they can freely import from both `MyProject/` and Mathlib. This makes it perfect for exploring new directions, testing hypotheses, or working on incomplete theorems without affecting the main codebase. Once a file in this folder reaches maturity and passes review, it can be moved to the appropriate location within `MyProject/` to become part of the core formalization.

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

## Development Environment

### VS Code Integration

The project is configured with optimal VS Code settings for Lean development:
- **Lean 4 extension** with syntax highlighting and goal display
- **Auto-formatting** on save following our style guidelines
- **Integrated terminal** for running blueprint commands
- **Git integration** for version control

### Key Commands

**Lean Development:**
```bash
lake build                    # Build the Lean project
lake exe cache get           # Download Mathlib cache (faster builds)
```

**Blueprint Documentation:**
```bash
leanblueprint all            # Compile PDF, web, and check declarations
leanblueprint serve          # Start local web server for blueprint
```

## Interactive Blueprint

### Viewing the Blueprint

Our mathematical exposition is available as an interactive web document at:

**[lean-summer-research.github.io/finalized/](https://lean-summer-research.github.io/finalized/)**

### What the Blueprint Provides

- **Mathematical exposition** written in LaTeX with proper mathematical notation
- **Lean integration** connecting each theorem to its formal proof
- **Dependency graph** showing relationships between definitions and theorems
- **Progress tracking** indicating which parts are formalized vs. planned
- **Responsive design** works on desktop and mobile devices

### Blueprint Features

- **Clickable definitions**: Jump between related concepts
- **Proof status indicators**: See what's proven vs. what needs work
- **Search functionality**: Find specific theorems or definitions
- **PDF export**: Download a traditional paper version

## Contributing

### Development Workflow

1. **Create a branch**: `git checkout -b feature/your-feature-name`
2. **Work in appropriate folder**:
   - `MyProject/` for finished, importable code
   - `WorkInProgress/` for experimental work
3. **Update documentation**: Modify corresponding `.tex` files in `LaTeX/`
4. **Test locally**: Run `leanblueprint all` to verify everything compiles
5. **Submit PR**: Push your branch and create a pull request