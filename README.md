
![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra is ZEro-knowledge algEBRA
Zeebra implements a subset of computational algebra and number theory for zero-knowledge cryptography.

## Why You Should Use Zeebra
As the saying goes, you can either make software so simple that it obviously has no bugs, or so complicated that it has no obvious bugs. Zeebra emphasizes clear documentation,  published references for algorithmic implementations, interoperability with Sage, and property-based testing for exhaustive test coverage.

### Status
- [x] Big Integers
- [x] Integer Factoring
- [x] Finite Field Arithmetic for Large Finite Fields
- [x] Univariate and Multivariate Polynomials over Finite Fields
- [x] Linear Algebra over Finite Fields
- [x] Number-Theoretic Transform (FFT over Finite Fields)
- [x] Grobner Bases
- [ ] Polynomial System Solving via Grobner Basis Algorithms

## Why You *Shouldn’t* Use Zeebra
I wrote Zeebra as an educational exercise. It is not yet complete or mature. It is not necessarily correct. For something more production-ready, please consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/tree/master)** - Algebraic structures and operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** - Linear Algebra library for the Rust programming language
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** - Arbitrary-precision numbers
- **[axect/peroxide](https://github.com/Axect/Peroxide)** - Linear algebra library for machine learning
