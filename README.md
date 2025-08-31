# Polynomial Sequences Formalization in Lean

This project provides a formalization of the theory of polynomial sequences in Lean 4, based on the principles of discrete calculus and finite differences.

## Motivation

The study of polynomial sequences is a classic topic in mathematics. A sequence `f(n)` is recognized as a polynomial in `n` of degree `d` if and only if its `d`-th finite difference is constant. This project aims to formalize this fundamental theorem and related concepts within the Lean 4 proof assistant.

The choice of the binomial coefficient basis, `(n k)`, is central to this project. This basis is particularly well-suited for the calculus of finite differences, as the forward difference operator `D` acts on these basis functions in a way that is analogous to how the standard derivative acts on monomials `x^k`. This elegance and simplicity make the binomial basis a natural choice for formalizing the theory of polynomial sequences.

By formalizing these concepts, we can rigorously verify the properties of polynomial sequences and build a library of results that can be used in other formalization projects, potentially in areas like combinatorics, number theory, or algorithm analysis.

## Summary of Results

The core of the project is located in the `PolynomialSequences/Basic.lean` file, which includes the main definitions and theorems.

### Key Concepts

-   **Polynomial Sequence**: A sequence `f` is defined as a polynomial sequence of degree `d` if its `n`-th term can be expressed as a linear combination of binomial coefficients:
    `f(n) = c₀ * (n 0) + c₁ * (n 1) + ... + c_d * (n d)`
    where the coefficients `c_k` are elements of a ring `R`. This is formalized in the `Sequence.Polynom` definition.

-   **Discrete Calculus**: We define two key linear operators:
    -   The **forward difference operator `D`**: `(D f)(n) = f(n+1) - f(n)`. This is the discrete analog of the derivative.
    -   The **indefinite sum operator `I`**: `(I f)(n) = Σ_{i=0}^{n-1} f(i)` (Defined recursively). This is the discrete analog of the integral.
    These operators have a simple and predictable effect on sequences expressed in the binomial basis.

### Main Theorems

The project formalizes the fundamental theorem of discrete calculus for polynomial sequences. This theorem establishes a strong connection between a sequence and its iterated differences. The main results are:

1.  **Equivalence of Polynomials and Constant Differences**: A sequence `f` is a polynomial sequence of degree `d` if and only if its `d`-th iterated difference, `D^[d] f`, is a constant sequence (i.e., a polynomial of degree 0). This is captured by the theorems `fundem1` and `fundem2`.

2.  **Binomial Coefficient Formula**: A formula is provided for the coefficients of a polynomial sequence in the binomial basis. The `k`-th coefficient `c_k` is given by the value of the `k`-th iterated difference of the sequence evaluated at `n=0`.
    `c_k = (D^[k] f)(0)`
    This gives a direct way to compute the representation of a polynomial sequence:
    `f(n) = Σ_{k=0}^{d} (D^[k] f)(0) * (n k)`
    This result, formalized in `fundem3`, is analogous to the Taylor series expansion of a function in continuous calculus, where coefficients are determined by derivatives at a point.

### Construction

The project also includes a constructive method, `Polyseq_mk`, for creating polynomial sequences from a given list of coefficients. This function is defined recursively and builds the sequence in a way that mirrors the properties of Pascal's triangle. For example, given coefficients `[c₀, c₁, c₂]`, it constructs a sequence whose values are determined by the recursive application of sums, ultimately proven to be equivalent to `c₀*(n 0) + c₁*(n 1) + c₂*(n 2)`. The `Polyseq_mk_soln` theorem proves that this construction indeed yields a valid polynomial sequence of the desired degree.

