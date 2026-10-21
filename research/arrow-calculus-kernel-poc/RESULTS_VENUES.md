# Venue Assessment for "No Translation Asymmetry Between Arrows and Lambda"

## Paper Summary

A 12-page paper (article format) proving a **negative result**: no translation
asymmetry exists between arrows and lambda (linear, compositional, law-preserving
translation, mechanized in Lean 4). It classifies three asymmetries—representation
(yes), expressive power (yes), translation (none)—and provides three lines of
evidence for the representation asymmetry: experimental (205 Rust tests),
engineering (221 Rust tests), and formal (19 Lean theorems, 0 sorry). The paper
honestly frames itself as "not a breakthrough; it is a rigorous elimination of a
conjectured asymmetry that clarifies the landscape."

**Key strengths:** substantial mechanization (Lean 4), large-scale experiments
(426 Rust tests total), honest framing, settles an open question, all 8
translation theorems fully mechanized (including the key compositionality
results for `>>>`, `first`, and `left`, the loop extension law under
fix-fusion, and the loop gap non-equivalence theorem), all 11 StructuralInfo
theorems fully mechanized — 19 Lean theorems total with zero `sorry` warnings.

**Key weaknesses:** negative result (not novel/constructive), some axioms
(confluence for STLC βη-reduction, type-inequality facts) are sound
meta-theorems assumed but not proved from first principles within Lean, the
engineering result shows the flat VM is still 4-10x slower than hand-written
code, the formal maximality claim was _falsified_ (honest but not a positive
theorem).

---

## Ranked Venues

### 1. Haskell Symposium 2026 (RECOMMENDED — Top Choice)

| Attribute      | Detail                                                                                                                                                                                                                                                                                                                                                                                                               |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Fit**        | **Excellent.** This is the natural home for arrow/monad calculus work. The paper's core citations—Hughes 2000, Lindley-Wadler-Yallop 2010, Kiselyov-Ishii 2015, VanDomelen et al. 2025—are all Haskell Symposium / JFP lineage. The community knows this literature intimately.                                                                                                                                      |
| **Deadline**   | May 21, 2026 (AoE) — ample time to polish the already-complete mechanization and presentation.                                                                                                                                                                                                                                                                                                                       |
| **Page limit** | 25 pages (new for 2026, acmsmall format). The 12-page paper fits easily; room to expand proofs and experiments.                                                                                                                                                                                                                                                                                                      |
| **Reputation** | Well-respected symposium (co-located with ICFP). Not as competitive as ICFP/POPL—better odds for a carefully-done negative result.                                                                                                                                                                                                                                                                                   |
| **Pros**       | Perfect scope match; community will appreciate the mechanization + experiments; the negative-result framing is appropriate here; 2026 PC chair (Lindsey Kuper) has PL/verification background; generous page limit; plenty of time to deadline; all 8 translation theorems fully mechanized including all compositionality results, the loop extension law, and the loop gap non-equivalence theorem (zero `sorry`). |
| **Cons**       | Less prestigious than ICFP/POPL; some axioms (confluence, type inequality) are sound but not proved from first principles within Lean.                                                                                                                                                                                                                                                                               |

### 2. MSFP 2026 — Mathematically Structured Functional Programming (Workshop)

| Attribute      | Detail                                                                                                                                                                                                                           |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Fit**        | **Excellent.** MSFP explicitly welcomes work on mathematical structures in functional programming—category theory, semantics, calculi. Negative results and boundary results are welcome at workshops.                           |
| **Deadline**   | May 7, 2026 (AoE, extended) — slightly before Haskell Symposium.                                                                                                                                                                 |
| **Page limit** | 15 pages (full paper, EPTCS proceedings) or 2 pages (extended abstract). The 12-page paper fits the full-paper track.                                                                                                            |
| **Reputation** | Well-regarded workshop (satellite of FSCD at FLoC 2026, Lisbon). EPTCS proceedings constitute a formal publication.                                                                                                              |
| **Pros**       | Perfect scope; lower barrier to acceptance; FLoC 2026 is a major event (co-located with IJCAR, CADE, FSCD, etc.); EPTCS proceedings; good venue for a "clarifies the landscape" paper; can later submit extended version to JFP. |
| **Cons**       | Workshop (less prestigious than a symposium); EPTCS is not ACM DL; slightly earlier deadline than Haskell Symposium; cannot submit to both MSFP and Haskell Symposium (double submission).                                       |

### 3. JFP — Journal of Functional Programming

| Attribute      | Detail                                                                                                                                                                                                                                                                                          |
| -------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Fit**        | **Excellent.** JFP scope explicitly includes "lambda calculi, rewriting, logic, type theory, category theory." The arrow calculus paper (Lindley-Wadler-Yallop 2010) was published in JFP.                                                                                                      |
| **Deadline**   | Rolling submission — no deadline.                                                                                                                                                                                                                                                               |
| **Page limit** | No fixed limit (short or long papers accepted).                                                                                                                                                                                                                                                 |
| **Reputation** | The journal for functional programming. Diamond open access (free to publish, free to read). ~3 month first decision.                                                                                                                                                                           |
| **Pros**       | Perfect scope; no deadline pressure; no page limit; diamond open access; can include full proofs and complete mechanization details; the arrow calculus lineage is here; good for a thorough, careful paper.                                                                                    |
| **Cons**       | No conference presentation (unless paired with one); longer review cycle; journals carry less "prestige signal" than top conferences for career advancement; no author response period.                                                                                                         |
| **Strategy**   | Ideal as a **follow-up** to a Haskell Symposium or MSFP acceptance: present the work at the venue, then submit an extended version (with full proofs, complete mechanization, expanded experiments) to JFP. JFP explicitly welcomes extended conference/workshop papers with ≥30% new material. |

### 4. ICFP 2026 — International Conference on Functional Programming

| Attribute      | Detail                                                                                                                                                                                                                                        |
| -------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Fit**        | **Good but risky.** ICFP covers FP theory, but tends to favor papers with language design, type system, or implementation contributions. A pure negative result with supporting evidence is unusual for ICFP.                                 |
| **Deadline**   | February 19, 2026 (AoE).                                                                                                                                                                                                                      |
| **Page limit** | 25 pages (PACMPL / acmsmall). Fits easily.                                                                                                                                                                                                    |
| **Reputation** | Top-tier FP conference. Highly competitive (~20-25% acceptance).                                                                                                                                                                              |
| **Pros**       | Top venue for FP; PACMPL publication (high impact); double-blind review; generous page limit.                                                                                                                                                 |
| **Cons**       | Very competitive; negative results struggle at top venues that want novelty; the Rust experiments are unusual for ICFP (which expects Haskell/OCaml/Scala); the "not a breakthrough" framing in the paper itself may work against acceptance. |

### 5. ESOP 2026 (Round 2) — European Symposium on Programming

| Attribute      | Detail                                                                                                                                       |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| **Fit**        | **Good.** ESOP welcomes formal PL theory, semantics, and calculi. The translation/asymmetry result is squarely in scope.                     |
| **Deadline**   | October 16, 2025 (Round 2). Round 1 (June 3, 2025) may have already passed.                                                                  |
| **Page limit** | ~25 pages (ETAPS standard). Fits easily.                                                                                                     |
| **Reputation** | Strong, well-respected (co-located with ETAPS). Competitive but less so than POPL/ICFP.                                                      |
| **Pros**       | Good scope match for the formal results; two-round scheme allows revision; ETAPS is a strong venue; the Lean mechanization is valued here.   |
| **Cons**       | The Rust experiments are unusual for ESOP (more theoretical venue); earlier deadline than Haskell/MSFP; European venue may limit attendance. |

---

## Also Considered (Not Ranked in Top 5)

| Venue           | Deadline                           | Assessment                                                                                                                                                                                                                                                                                                                                                                                                              |
| --------------- | ---------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **POPL 2026**   | July 10, 2025                      | **Deadline likely passed.** Would need to target POPL 2027 (deadline ~July 2026). Top-tier but very competitive; negative results face an uphill battle. The formal boundary result is POPL-appropriate, but the Rust experiments are not.                                                                                                                                                                              |
| **OOPSLA 2026** | R1: Oct 10, 2025; R2: Mar 17, 2026 | Broad PL venue, very competitive. The paper lacks the broad appeal OOPSLA seeks. Not a natural fit.                                                                                                                                                                                                                                                                                                                     |
| **PLDI 2026**   | Nov 13, 2025                       | The speculative compilation engineering result is interesting but not the main contribution. PLDI wants systems/implementation papers with stronger performance results. The flat VM being 4-10x slower than hand-written code undercuts the PLDI pitch.                                                                                                                                                                |
| **CPP 2026**    | Sep 12, 2025 (abstract Sep 5)      | Focuses on mechanized proofs. All 19 Lean theorems are now fully mechanized with zero `sorry` — this is a strong fit for CPP, which expects complete mechanization. The StructuralInfo.lean module (11 theorems, 0 sorry) and all 8 Translation.lean theorems are fully proved. Some axioms (confluence, type inequality) are sound meta-theorems rather than proved from first principles, which is standard practice. |
| **TYPES 2026**  | Jan 20, 2026                       | Only 2-page extended abstracts (contributed talks). Not a full-paper venue. Good for presenting the Lean formalization and getting feedback, but not for publishing the full result. Could be a good "stepping stone" presentation.                                                                                                                                                                                     |
| **LMCS**        | Rolling                            | Good for formal results with logical content, but the paper is more FP/calculus than logic. 50-page limit. Open access. A viable journal alternative to JFP if the paper is framed around the formal σ measure and ordering theorems.                                                                                                                                                                                   |
| **TOPLAS**      | Rolling                            | Extremely prestigious but very long review process (6-12+ months) and highly selective. Not appropriate for this paper's current strength level.                                                                                                                                                                                                                                                                        |

---

## Recommendation

### Top choice: **Haskell Symposium 2026**

The Haskell Symposium is the best fit for this paper. The arrow calculus lineage
lives here (Hughes, Lindley-Wadler-Yallop, Kiselyov, VanDomelen all published in
this community). The 2026 page limit increase to 25 pages (acmsmall) gives room
to expand the 12-page draft with complete proofs and additional experimental
detail. The May 21, 2026 deadline provides ample time to:

1. Reformat to acmsmall.
2. Polish the presentation for the Haskell community audience.
3. Optionally, prove the sound axioms (confluence, type inequality) from first
   principles within Lean for an even stronger mechanization — though these are
   standard meta-theorems and their assumption is well-justified.

The negative-result framing is appropriate for the Haskell Symposium, which
values rigor and careful analysis over headline-grabbing claims. The community
will appreciate the honest assessment and the substantial supporting evidence.

### Backup strategy: **MSFP 2026 → JFP**

If the Haskell Symposium submission is not accepted, or if the authors prefer a
workshop venue with lower competition:

1. Submit to **MSFP 2026** (deadline May 7, 2026, 15-page limit, EPTCS
   proceedings) as a full paper. MSFP is an excellent venue for mathematically
   structured work and welcomes boundary/clarification results.
2. After MSFP acceptance and presentation, submit an **extended version to JFP**
   with full proofs, complete mechanization, and expanded experimental detail
   (≥30% new material per JFP policy).

### Not recommended: ICFP, POPL, PLDI, OOPSLA

These top-tier venues are not the right fit for this paper in its current form.
The paper is honest that it is "not a breakthrough"—top venues want
breakthroughs. The negative result, while valuable, is better suited to a
venue that values careful landscape clarification.

---

## Honest Assessment: Is This Paper Strong Enough for a Top Venue?

**No, not in its current form.** Here is the candid evaluation:

**What would need to change for a top venue (ICFP/POPL):**

- The mechanization is now complete (all 19 Lean theorems, all 8 translation
  theorems, zero `sorry`). The remaining formal gap is that some axioms
  (confluence for STLC βη-reduction, type-inequality facts) are sound
  meta-theorems assumed rather than proved from first principles within Lean —
  standard practice, but top venues with formal claims may prefer fully
  axiom-free proofs.
- The negative result needs to be framed as more than "elimination of a
  conjecture." Top venues want _surprising_ results or _new techniques_. The
  linearity bound (8x) and compositionality (by `rfl`) are technically
  straightforward—reviewers may see them as "expected" rather than "settling an
  open question."
- The engineering result (speculative compilation, 3.5-5x speedup) is
  interesting but the flat VM is still 4-10x slower than hand-written code.
  This undercuts the practical significance claim.
- The maximality claim was _falsified_—honest, but reviewers at top venues may
  read this as "the interesting conjecture was wrong."

**What the paper does well:**

- The three-lines-of-evidence structure (experimental, engineering, formal) is
  thorough and well-organized.
- The honest framing is refreshing and scientifically valuable.
- The σ measure and ordering theorem are a genuine formal contribution.
- 426 Rust tests provide strong empirical backing.
- The "boundary crossing point" characterization is a useful conceptual
  contribution.

**Bottom line:** This is a solid, careful paper that clarifies an important
landscape question. It is **well-suited for the Haskell Symposium or MSFP**,
where rigor and community relevance matter more than novelty. The mechanization
is now complete (all 19 Lean theorems, zero `sorry`), which strengthens the
formal contribution. With stronger framing, it could potentially target ICFP,
but the negative-result nature will always be a headwind at top venues. The best
long-term home is **JFP** as an extended journal version after conference
presentation.
