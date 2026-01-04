# FAA 2025 Class Projects

Formalization of Analysis of Algorithms - ETH Zurich

## Checklist
- [x] Full implementation of Treap operations and correctness
    - [x] Basic definitions
    - [x] Split
    - [x] Merge
    - [x] Insert, delete, Build (optional if you want)
- [ ] Decide what to do with different or equal keys / prios
- [ ] Time complexity of all operations, based on split/merge
    - [x] Leftmost
    - [x] Split
    - [x] Merge
    - [ ] Insert, delete, Build (optional)
- [ ] RandomizedTreap, prove that expected height is O(log N)

## Quick Start

```bash
git clone https://github.com/sorrachai/FAA2025_class_projects.git
cd FAA2025_class_projects
lake exe cache get
lake build
```

## Workflow

### Create your branch
```bash
git checkout -b project1-yourname
```

### Work on your project
Create a new folder named after your last name. 
Edit files in `Projects/[LastName]/`

### Test locally
```bash
lake build
```

### Submit
```bash
git add .
git commit -m "Complete Project 1"
git push origin project1-yourname
```

Then create a Pull Request on GitHub.

## CI Checks

Automatic checks on every push:

- **Build**: Must compile successfully
- **Sorry count**: Number of incomplete proofs
- **Axiom usage**: Custom axioms are not allowed
- **Linter**: Code quality warnings

## Resources

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
