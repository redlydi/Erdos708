# Lean verification status — Erdős problem 708

**Status as of 2026-11-25.** This table distinguishes written arguments, finite computation and Lean proof.

| Statement | Source | Lean status |
|---|---|---|
| Support membership, containment, antitone property, prime-power nesting, cardinality bound | `Erdos708Formal/Support.lean` | **Lean source supplied; CI compile pending** |
| Concrete local collision at 210 | `Erdos708Formal/Support.lean` | **Lean source supplied; CI compile pending** |
| Global support-width bound τ(A,I) ≤ Σ w(a), laminar corollary | `REPORT.md` §3 (outside this starter) | **Not formalized** |
| Bounded-core bound τ(A,I) ≤ 2n+C(k) | `REPORT.md` §1 | **Not formalized** |
| Coprime-core cycle bound τ(A,I) ≤ 2n−1+f | `REPORT.md` §2 | **Not formalized** |
| Pairwise-coprime alphabet rank-three bound | `REPORT.md` §4 | **Not formalized** |
| G2 exact result and G3 certificates | Earlier project reports and Python programs | **Not formally verified here** |
| Historical lower bound for 15 moduli and finite witness | `legacy/Erdos708.lean` | **Existing Lean source preserved unmodified; not included in default build; needs fresh successful independent compile** |
| General asymptotic claim g(n) ≤ (2+o(1))n | Open target | **Not proved** |

Important: The default GitHub Actions job compiles `Erdos708Formal` and its imports only. It does not certify the original research claims. The legacy certificate can be tested separately by dispatching the workflow with `verify_legacy=true`.

If the first GitHub Action fails, fix that precise build problem and re-run. Do not mark a claim Lean-verified before the job passes.
