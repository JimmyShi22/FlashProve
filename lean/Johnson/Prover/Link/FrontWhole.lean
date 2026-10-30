-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontWhole.lean: THE LINK's FRONT, ITS VALUES' HALF, WHOLE: behind the batching
the claim holds at mu0 of the two tables' folds. It joins front_claim (FrontClaim.lean), src_st4R
(FrontWritten.lean) and mu0's laws (FrontMsg.lean). Statements and proofs.

  frontMsg S t γ M₀ M₁ fr   mu0 of the two members' messages: the folds at γ; fr elsewhere
  smAt S t σ μ a            the sample's row of member a at the seed σ, at μ's share: what an honest
                            answer is
  answOf_written            where round 3 shows the two written values, the library reads them back
  front_holds               head_claimR's own premises · a row of the group's code has 2 ^ aP places
                            · the two stored strings are the tables of M₀'s and M₁'s rows' code
                            words
                            · the OOD samples hold the rows' answers · the tables agree on the
                            entries that are compared · round 3 shows ofE (smAt ...) for the two
                            members
                            ⟹ (Slf.idf).Holds (stmG (S.sg t₀) row) (frontMsg ...), WHATEVER fr

WHERE hR AND hB MUST COME FROM: hR (LinkRanR) from k15_ran (Johnson/Desc/K15/K15Law.lean), which
wants the yes of the link's SIX FRONT BLOCKS alone; hB (BatRan) from batRan_at
(Johnson/Desc/K15/K15Head.lean), which wants that the batching returns a row. NOT from linkClaim
(K15Head.lean): its premise is the whole decision's yes, which is what this folder is after.
The carried mask row: mu0 lays 0 there, and hmask says that the batched row's coefficients there
read 0; for the claim's value either alone would do; mu0's 0 is for the word that a later law reads
there.

Not shown here. That a run meets head_claimR's premises: that the six front blocks say yes on an
honest view is not stated here (at the full size it is had on the way to link_yes:
front6_walks_full, FormWalks.lean, called in LinkJoinE.lean). That D's coding's tables and OOD
samples are such M₀, M₁ (at the goals' input: meant_home, Johnson/Goal/Conditions/LinkMeant.lean).
Nothing on the written oracle of round 2: the tails of the group's rows under the group's own code,
the first fold's mask that goes out beside the two folds, and what a verifier reads of that tree are
made nowhere here. Nothing on soundness; nothing on what any entry of a message discloses or does
not disclose. TWO SHAPES: that under hR, hS and hF the sizes have t0 + T.r + 1 ≤ R * C.l is said by
padRoom_of_ran (Johnson/Prover/Link/PadRoomOfRan.lean [not in this library]): nothing in this
library shows it; if it holds, the two shapes at which membMsg (FrontMsg.lean) does not read fr at
the pad's place cannot occur there: both have t0 + T.r = R * C.l.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontClaim
import Johnson.Prover.Link.FrontWritten
import Johnson.Prover.Link.FrontMsg

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb Cb.Ood Iop _root_.Run
open OnBytes.Params (LinkShape)

/-- **The group's message at the folds.** -/
noncomputable def frontMsg (S : Sz) (t : ℕ) (γ : Fin S.P.v → GE)
    (M₀ M₁ : (Fin S.P.v → Bool) → S.Co → GE) (fr : Bool → S.MJ → GE) : (S.sg t).cIn.J → GE :=
  mu0 S t fun a => membMsg S (foldAll γ (if a then M₁ else M₀)) (fr a)

/-- The sample's row of member a at a seed, at μ's share. -/
noncomputable def smAt (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (μ : (S.sg t).cIn.J → GE)
    (a : Bool) : GE :=
  ∑ j, (S.fam.om a).Z.mat σ () j * μ (atJ S t a j)

/-- Two written answers are read back. -/
theorem answOf_written (S : Sz) (d : PQ.RD) (m : (wRound d).Msg) (v₀ v₁ : GE)
    (h : PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2) =
      [.answer (ofE v₀), .answer (ofE v₁)]) (a : Bool) :
    answOf S d m a () = if a then v₁ else v₀ := by
  unfold answOf OnBytes.Slice.ansOf
  rw [h]
  cases a
  · show toE (ofE v₀) = v₀
    exact toE_ofE v₀
  · show toE (ofE v₁) = v₁
    exact toE_ofE v₁

/-- **Behind the batching the claim holds at the folds.** -/
theorem front_holds (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (d1 d2 d3 d4 d5 dA : PQ.RD)
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
    (c c' cd : Ctx) (x : LinkRun) (D : LinkDataR) (G0 : Group) (L : GroupLayout)
    (θ : E) (row : GroupRow) (hS : LinkSizes S Λ c.st.codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hR : LinkRanR Λ first further c c' x D) (hB : BatRan x.group c' cd G0 L θ row)
    (a1 : D.r1 = rvW d1 m1 c1) (a2 : D.r2 = rvW d2 m2 c2) (a3 : D.r3 = rvW d3 m3 c3)
    (a4 : D.r4 = rvW d4 m4 c4) (a5 : D.r5 = rvW d5 m5 c5)
    (hop : ∀ o ∈ c.ch.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hmask : ∀ i, i < S.P.Z.l → readV row.d i = 0)
    (hl2 : S.P.C.l = 2 ^ S.P.aP)
    (M₀ M₁ : (S.ixR (recZ S.P.T.l lg n)).Row → S.Co → GE) (fr : Bool → S.MJ → GE)
    (rec0 : ∀ ρ s, r.1.2 (ρ, s) =
      ∑ j, (recZ S.P.T.l lg n).mat r.1.1 s j * M₀ ρ ((S.ixR (recZ S.P.T.l lg n)).pl j))
    (rec1 : ∀ ρ s, r.2.2 (ρ, s) =
      ∑ j, (recZ S.P.T.l lg n).mat r.2.1 s j * M₁ ρ ((S.ixR (recZ S.P.T.l lg n)).pl j))
    (tab0 : (S.lkR (recZ S.P.T.l lg n)).tab y.1 =
      fun ρ => (S.ixR (recZ S.P.T.l lg n)).G.mulVec (M₀ ρ))
    (tab1 : (S.lkR (recZ S.P.T.l lg n)).tab y.2 =
      fun ρ => (S.ixR (recZ S.P.T.l lg n)).G.mulVec (M₁ ρ))
    (same : (S.lwR (recZ S.P.T.l lg n)).SameOn ((S.ixR (recZ S.P.T.l lg n)).view M₀)
      ((S.ixR (recZ S.P.T.l lg n)).view M₁))
    (hans : PQ.PlainOf.gots d3.items (GPlain.old (b := d3.entry.work) m3.2) =
      [.answer (ofE (smAt S t₀ (gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2))
          (frontMsg S t₀ (gVec S.P.v _ (valsOf d1 c1)) M₀ M₁ fr) false)),
        .answer (ofE (smAt S t₀ (gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2))
          (frontMsg S t₀ (gVec S.P.v _ (valsOf d1 c1)) M₀ M₁ fr) true))]) :
    (Slf.idf (E := GE) (J := (S.sg t₀).cIn.J)).Holds (stmG (S.sg t₀) row)
      (frontMsg S t₀ (gVec S.P.v _ (valsOf d1 c1)) M₀ M₁ fr) := by
  refine front_claim S t₀ lg n Λ first further d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
    c c' cd x D G0 L θ row hS hF hd hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hR hB a1 a2 a3 a4 a5 hop
    hmask hl2 _ M₀ M₁ (src_st4R S _ r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5 t₀ _ M₀ M₁
      (free_mu0 S t₀ _) (fun k => ?_) (fun k => ?_) rec0 rec1 tab0 tab1 same fun a => ?_)
  · exact (mu0_atJ S t₀ _ false _).trans (membMsg_putAt S _ _ k)
  · exact (mu0_atJ S t₀ _ true _).trans (membMsg_putAt S _ _ k)
  · rw [answOf_written S d3 m3 _ _ hans a]
    cases a <;> rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.frontMsg
#print axioms Johnson.Prover.Link.smAt
#print axioms Johnson.Prover.Link.answOf_written
#print axioms Johnson.Prover.Link.front_holds
