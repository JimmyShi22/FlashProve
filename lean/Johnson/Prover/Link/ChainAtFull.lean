-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainAtFull.lean: THE CLOSED FACTS ON PUBLIC DATA THAT THE DECISION's YES AT THE
FRAME's VIEW ASKS (Johnson/Prover/Link/ChainWhole.lean), AT THE COPY's FILE's WRITTEN LETTERS, both
sizes: the rounds' data dsFull | dsSmall (OnBytes/Flat/LinkSibAt.lean), the external openings
frD.xs | srD.xs, the stored strings' depth frS.P.T.a | srS.P.T.a, against the description's own
declared rounds linkDeclaredRounds frP | linkDeclaredRounds srP (Johnson/Desc/Link/LinkWritten.lean). Statements and
proofs; each closed fact by the kernel's evaluation of a test with code.

  isOf2B, forall₂_isOf2, all_nz, all_opens   three of the facts as tests with code
  fr_isOf2, fr_nz, fr_wantTie, fr_wideTie, fr_opens   the five at the full size (41 rounds; depth
                  32; a stored column has 2048 words)
  sr_isOf2, sr_nz, sr_wantTie, sr_wideTie, sr_opens   the five at the small size (24 rounds; depth
                  23; 256 words)
  run_viewOf_full, run_viewOf_small   run_viewOf_at at these letters: WHAT IS LEFT: the tests on the
                  plan and the instance · the words' test at the view · the widths of next's columns
                  and of the two stored strings' columns · the blocks' decisions in a row · the last
                  test

Each of the ten closed facts stands under "set_option maxRecDepth 100000 in", as the library's own
closed facts at these letters do (Johnson/Desc/K15/TypedV.lean): a limit of elaboration is raised;
the kernel checks the term.

Limits. Public numbers alone. What is left is left: no block's yes is shown here. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainWhole
import Johnson.Desc.K15.TypedV
import Johnson.Desc.Link.LinkWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc Desc.K15
open OnBytes (TableKey)
open OnBytes.Flat (dsFull dsSmall)
open OnBytes.Slice (frD srD frS srS)
open _root_.Run.PQ (XO SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)

/-- IsOf2, as a test with code. -/
def isOf2B (d : Fmt.DeclaredRound) (w : RD) : Bool :=
  w.entry == d.entry && w.items == d.items && Fmt.kindOf d.entry.name == some w.kind

theorem forall₂_isOf2 : ∀ (decls : List Fmt.DeclaredRound) (ds : List RD),
    (decls.length == ds.length && (decls.zip ds).all fun p => isOf2B p.1 p.2) = true →
    List.Forall₂ IsOf2 decls ds
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | d :: decls, w :: ds, h => by
    simp only [List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq,
      isOf2B] at h
    obtain ⟨hl, ⟨⟨e1, e2⟩, e3⟩, hr⟩ := h
    exact List.Forall₂.cons ⟨e1, e2, e3⟩ (forall₂_isOf2 decls ds (by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨Nat.succ.inj hl, hr⟩))

theorem all_nz (decls : List Fmt.DeclaredRound)
    (h : (decls.all fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)) = true) :
    ∀ d ∈ decls, d.entry.drawNZ ≤ d.entry.drawE := fun d hd =>
  of_decide_eq_true (List.all_eq_true.1 h d hd)

theorem all_opens (ds : List RD) (h : (ds.all fun d => d.opens.all (· < 2 ^ 16)) = true) :
    ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16 := fun d hd n hn =>
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h d hd) n hn)

/-! ## The full size -/

set_option maxRecDepth 100000 in
theorem fr_isOf2 : List.Forall₂ IsOf2 (linkDeclaredRounds frP) dsFull :=
  forall₂_isOf2 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem fr_nz : ∀ d ∈ linkDeclaredRounds frP, d.entry.drawNZ ≤ d.entry.drawE := all_nz _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem fr_wantTie : wantTie frS.P.T.a dsFull frD.xs (linkDeclaredRounds frP) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_wideTie : wideTie dsFull (fun _ => 2048) (linkDeclaredRounds frP) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_opens : ∀ d ∈ dsFull, ∀ n ∈ d.opens, n < 2 ^ 16 := all_opens _ (by decide +kernel)

/-! ## The small size -/

set_option maxRecDepth 100000 in
theorem sr_isOf2 : List.Forall₂ IsOf2 (linkDeclaredRounds srP) dsSmall :=
  forall₂_isOf2 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sr_nz : ∀ d ∈ linkDeclaredRounds srP, d.entry.drawNZ ≤ d.entry.drawE := all_nz _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sr_wantTie : wantTie srS.P.T.a dsSmall srD.xs (linkDeclaredRounds srP) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sr_wideTie : wideTie dsSmall (fun _ => 256) (linkDeclaredRounds srP) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sr_opens : ∀ d ∈ dsSmall, ∀ n ∈ d.opens, n < 2 ^ 16 := all_opens _ (by decide +kernel)

/-! ## The decision's yes at the written letters -/

/-- **At the full size.** -/
theorem run_viewOf_full (plan : List Fmt.DeclaredRound) (ok : Bool) (x : TableKey × TableKey)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (ρ : Rho (uL (ckP .two) dsFull)) (e : (linkDescriptionAt frP plan ok).S)
    (hp : (linkDescriptionAt frP plan ok).planWord = none) (ho : (linkDescriptionAt frP plan ok).okStart x = true)
    (hv : viewWordsBelowPrime (viewOf dsFull frS.P.T.a frD.xs next y (drawnSL (ckP .two) dsFull ρ)) = true)
    (hW : ∀ j k d s, dsFull[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
      ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048)
    (hk : Walks 0 (lookV dsFull frS.P.T.a next y (drawnSL (ckP .two) dsFull ρ))
      (linkDescriptionAt frP plan ok).chain.blocksInOrder ((linkDescriptionAt frP plan ok).start x)
      (rvOf dsFull 0 [] next (drawnSL (ckP .two) dsFull ρ)) e)
    (he : (linkDescriptionAt frP plan ok).fin x e = true) :
    (linkDescriptionAt frP plan ok).run x
      (viewOf dsFull frS.P.T.a frD.xs next y (drawnSL (ckP .two) dsFull ρ)) = true :=
  run_viewOf_at (linkDescriptionAt frP plan ok) x dsFull frS.P.T.a frD.xs next y ρ e (fun _ => 2048) hp ho hv
    fr_isOf2 fr_nz fr_wantTie fr_wideTie fr_opens hW hy hk he

/-- **At the small size.** -/
theorem run_viewOf_small (plan : List Fmt.DeclaredRound) (ok : Bool) (x : TableKey × TableKey)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ srS.P.T.a) SgX).Str)
    (ρ : Rho (uL (ckP .two) dsSmall)) (e : (linkDescriptionAt srP plan ok).S)
    (hp : (linkDescriptionAt srP plan ok).planWord = none) (ho : (linkDescriptionAt srP plan ok).okStart x = true)
    (hv : viewWordsBelowPrime (viewOf dsSmall srS.P.T.a srD.xs next y (drawnSL (ckP .two) dsSmall ρ)) = true)
    (hW : ∀ j k d s, dsSmall[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ srS.P.T.a),
      ((twoExternalStrings (2 ^ srS.P.T.a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 256)
    (hk : Walks 0 (lookV dsSmall srS.P.T.a next y (drawnSL (ckP .two) dsSmall ρ))
      (linkDescriptionAt srP plan ok).chain.blocksInOrder ((linkDescriptionAt srP plan ok).start x)
      (rvOf dsSmall 0 [] next (drawnSL (ckP .two) dsSmall ρ)) e)
    (he : (linkDescriptionAt srP plan ok).fin x e = true) :
    (linkDescriptionAt srP plan ok).run x
      (viewOf dsSmall srS.P.T.a srD.xs next y (drawnSL (ckP .two) dsSmall ρ)) = true :=
  run_viewOf_at (linkDescriptionAt srP plan ok) x dsSmall srS.P.T.a srD.xs next y ρ e (fun _ => 256) hp ho hv
    sr_isOf2 sr_nz sr_wantTie sr_wideTie sr_opens hW hy hk he

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.forall₂_isOf2
#print axioms Johnson.Prover.Link.all_nz
#print axioms Johnson.Prover.Link.all_opens
#print axioms Johnson.Prover.Link.fr_isOf2
#print axioms Johnson.Prover.Link.fr_nz
#print axioms Johnson.Prover.Link.fr_wantTie
#print axioms Johnson.Prover.Link.fr_wideTie
#print axioms Johnson.Prover.Link.fr_opens
#print axioms Johnson.Prover.Link.sr_isOf2
#print axioms Johnson.Prover.Link.sr_nz
#print axioms Johnson.Prover.Link.sr_wantTie
#print axioms Johnson.Prover.Link.sr_wideTie
#print axioms Johnson.Prover.Link.sr_opens
#print axioms Johnson.Prover.Link.run_viewOf_full
#print axioms Johnson.Prover.Link.run_viewOf_small
