# LeanM2

*A verified bridge between Lean 4 and Macaulay2.*

LeanM2 lets you call the powerful computer-algebra system **Macaulay2** from inside
Lean 4 **tactics** and turn the answers it returns (e.g. Gröbner‐basis computations,
ideal-membership certificates, …) into *formal Lean proofs* that the kernel
accepts.  
It is therefore a first step toward making heavyweight algebraic geometry and
commutative-algebra automation both fast *and* trustworthy in formal settings.


- **Lean / mathlib** can state and verify deep theorems but is not optimized for CAS-like symbolic computations at scale.
- **Macaulay2** is extremely fast at Gröbner bases, primary decompositions, and many other CAS utilities. However, it offers no formal guarantees beyond its own testing.

LeanM2 combines the two by shipping the goal state to M2,
  parsing the reply, and synthesising a Lean proof term that witnesses the
  result.

---

## Features

| Area | Status |
|------|--------|
| Ideal-membership tactic (`by m2`) | ✅  Uses Gröbner bases + change-of-basis matrix returned by M2 to produce a certified equality proof, far extending the functionality of polyrith. |
| Type bridges (`M2Type` class, parser, and infrastructure) | ✅  Coercions for elements and polynomials of ℤ, ℚ, ℝ, ℂ, finite fields, polynomial rings, and quotient rings (and nested versions of the aforementioned!) between Lean and M2 |
| Additional M2 functionality (Hilbert series, radicals, …) | ⏳ In Progress! |

---

## Quick start

### 0 . Prerequisites

| Tool | Minimum version | Notes |
|------|-----------------|-------|
| **Lean 4** | 4.16.0 (or newer) | |
| **Macaulay2** | 1.22 | Needs to be on `$PATH` so LeanM2 can shell out |
| **Mathlib** | Matching Lean version | |
| **Scilean** | Matching Lean version | on `blas` branch |
### 1 . Clone & build

```bash
git clone https://github.com/riyazahuja/lean-m2.git
cd lean-m2
lake exe cache get   # fetch mathlib4 etc.
lake build
```

Or, insert LeanM2 into your `lakefile.lean` or `lakefile.toml` directly and include `import LeanM2.Tactic`! 

### 2 . Try it!

Run `Examples/leanM2Demo.lean` to see some basic examples of LeanM2 in action for solving ideal membership questions over a large range of base rings. We hope to continue port over Macaulay2 and other CAS functionality to Lean (with proof certificates!) as this project progresses. Stay tuned!

---

## How it works (overview)

The core of LeanM2 centers around the conversion of Lean structures, definitions, and datatypes into valid Macaulay2 syntax, and vice versa. This is done as follows:

1. **Goal Analysis** – The tactic parses the current goals to determine if the goal is supported by Macaulay2 (for now, only ideal membership questions are allowed).
2. **M2 Conversion** - If the goal is supported, we check if the rings, ideals, polynomials, etc. are supported for M2 syntax conversion (instances `M2Type`). We then lift each of these objects into their Macaulay2-supported objects (`M2Expr`, ...), which have `ToString` methods to convert automatically into valid Macaulay2 code.
2. **M2 round-trip** – The reified code is pretty-printed to an M2 command,
   executed, and its textual reply is parsed (`LeanM2.parser`) back into the Lean objects.
3. **Certificate synthesis** – For ideal membership we combine the change-of-basis
   matrix M2 returns with mathlib’s algebraic API to build a Lean term witnessing
   equality in the ideal. For other M2 tools, we similarly hope to construct explicit proof witnesses for use in Lean.
4. **Tactic closes goal** – The generated term is checked by the Lean kernel to close the current goal.


---

## Roadmap

- Support more M2 subsystems (primary decomposition, Hilbert polynomials, …) and types.
- Broader type bridge (schemes, graded modules).
- Streamlined UX (a `simp`-like tactic interface that handles a variety of goals).
- Performance: Eliminate python middle layer, pool M2 processes, incremental certificates.


---

## Contributing

Bug reports, feature requests, and PRs are welcome! Contact us at `riyaza@andrew.cmu.edu`.

--- 

## Acknowledgements

LeanM2 grew out of my CMU 21-849 final project “Grobner Bases: Theory & Practice”.
Thanks to Dennis Chen and Rohan Jain for early discussions, Tomáš Skřivan for SciLean help, and to the Mathlib community for its invaluable ecosystem. 

