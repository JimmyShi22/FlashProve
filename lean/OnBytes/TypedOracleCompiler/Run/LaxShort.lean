-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxShort.lean: the lax verifier's evaluable form along a short list of positions.

Why. `verifyLX` (OnBytes/TypedOracleCompiler/Run/LaxThin.lean) walks `wq.ext.all`, the list of all positions of the
external strings, and takes those that are read. At the full size of the entry file (`recordGround`,
OnBytes/Tie/EntryGrounds.lean) that list has 2 * 2 ^ 32 members. Here is a form that walks a short
list. OnBytes/RunA/ListedDefs.lean has the like for the strict verifier of the library's own
compiler (`verifyPL`); `verifyPL` is over that compiler's types, and nothing of that file is used
here.

  `eq_of_sorted_mem`: two lists that increase strictly under a key and have the same members are one
    list.
  `extLP_filter`: `extLP` takes of a list the read positions alone.
  `extLP_wire`: `extLP` reads of a wire its fields leaf, which and depth alone.
  `afterLX_listed`: `afterLX` has one value at two wires that agree in all that it reads but the
    list of all positions, and at two right tests of whether a position is read, if both lists
    increase strictly under one key, the first holds every position and the second every read
    position.
  `verifyLXL`: `verifyLX`'s text, with a list made of the instance and the verifier's messages in
    the place of the long list. It tests at run time that this list increases strictly and holds
    every read position. The wire comes as its own part sh and a function wqOf from a list to a
    wire, so that a caller need not name a record that holds the long list. The list is trusted for
    nothing: a list that fails a test makes the function say no.
  `verifyLXL_yes`: a yes of `verifyLXL` is a yes of `verifyLX` at a wire wq, if wq's own list
    increases strictly under the key and holds every position, wqOf L is wq with L as its list, and
    both tests are right.
What is not claimed: the other direction (OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean has it, for a
list that always passes the two tests). Any time or memory. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.LaxThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

/-- Two lists that increase strictly under a key and have the same members are one list. -/
theorem eq_of_sorted_mem {α : Type} (key : α → ℕ) :
    ∀ (l₁ l₂ : List α), l₁.Pairwise (fun a b => key a < key b) →
      l₂.Pairwise (fun a b => key a < key b) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: t₁, b :: t₂, s₁, s₂, h => by
      obtain ⟨ha, s₁'⟩ := List.pairwise_cons.1 s₁
      obtain ⟨hb, s₂'⟩ := List.pairwise_cons.1 s₂
      have hab : a = b := by
        rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | m
        · exact e
        · rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e' | m'
          · exact e'.symm
          · have h1 := hb a m
            have h2 := ha b m'
            omega
      subst hab
      congr 1
      refine eq_of_sorted_mem key t₁ t₂ s₁' s₂' fun x => ⟨fun m => ?_, fun m => ?_⟩
      · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ m)) with e | m'
        · subst e
          exact absurd (ha x m) (lt_irrefl _)
        · exact m'
      · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ m)) with e | m'
        · subst e
          exact absurd (hb x m) (lt_irrefl _)
        · exact m'

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X)

/-- `extLP` takes of a list the read positions alone. -/
theorem extLP_filter {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ()))
    (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ l : List E.Pos,
      extLP Lf we emb cms isRead f l = extLP Lf we emb cms isRead f (l.filter isRead)
  | [] => rfl
  | p :: ps => by
      by_cases h : isRead p = true
      · rw [List.filter_cons_of_pos h]
        simp only [extLP, h, if_true]
        rw [extLP_filter we emb cms isRead f ps]
      · rw [List.filter_cons_of_neg h]
        simp only [extLP, h]
        exact extLP_filter we emb cms isRead f ps

/-- `extLP` reads of a wire its fields leaf, which and depth alone. -/
theorem extLP_wire {E : ExtSpec} (we we' : WireE E) (hl : we'.leaf = we.leaf)
    (hw : we'.which = we.which) (hd : we'.depth = we.depth) (emb : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ l : List E.Pos, extLP Lf we' emb cms isRead f l = extLP Lf we emb cms isRead f l
  | [] => rfl
  | p :: ps => by
      simp only [extLP, hl, hw, hd, extLP_wire we we' hl hw hd emb cms isRead f ps]

variable (g : Fam (typedOracleFamily lam K (Lf ())))
variable {Y : Type} {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)
  {M' : Type} (mk' : Finset E.Pos → M') (tst' : M' → E.Pos → Bool)

/-- `afterLX` has one value at two wires that agree in all that it reads but the list of all
positions, and at two right tests of whether a position is read, under the premises on the two lists
that stand in the statement. -/
theorem afterLX_listed (P : PS Y E) (wq wq' : ProtocolQueryLayout lam K P.up) (hsh : wq'.sh = wq.sh)
    (hl : wq'.ext.leaf = wq.ext.leaf) (hw : wq'.ext.which = wq.ext.which)
    (hd : wq'.ext.depth = wq.ext.depth) (hb : wq'.ext.build = wq.ext.build)
    (hn : wq'.nOpen = wq.nOpen) (hm : wq'.maxDepth = wq.maxDepth)
    (key : E.Pos → ℕ) (s : wq.ext.all.Pairwise (fun a b => key a < key b))
    (hall : ∀ p, p ∈ wq.ext.all) (htst : ∀ R p, tst (mk R) p = true ↔ p ∈ R)
    (htst' : ∀ R p, tst' (mk' R) p = true ↔ p ∈ R)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam)
    (s' : wq'.ext.all.Pairwise (fun a b => key a < key b))
    (hcov : ∀ p, tst (mk (P.extReads x ρ)) p = true → p ∈ wq'.ext.all) :
    afterLX Lf g mk' tst' P wq' embS embE depthReq cms x π ρ rts ph =
      afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph := by
  have ht : tst' (mk' (P.extReads x ρ)) = tst (mk (P.extReads x ρ)) :=
    funext fun p => Bool.eq_iff_iff.2 ((htst' _ p).trans (htst _ p).symm)
  have e : extLP Lf wq'.ext embE cms (tst' (mk' (P.extReads x ρ))) π.ext wq'.ext.all =
      extLP Lf wq.ext embE cms (tst (mk (P.extReads x ρ))) π.ext wq.ext.all := by
    rw [ht, extLP_wire Lf wq.ext wq'.ext hl hw hd, extLP_filter Lf wq.ext _ _ _ _ wq'.ext.all,
      extLP_filter Lf wq.ext _ _ _ _ wq.ext.all]
    congr 1
    refine eq_of_sorted_mem key _ _ (s'.filter _) (s.filter _) fun p => ?_
    simp only [List.mem_filter]
    exact ⟨fun h => ⟨hall p, h.2⟩, fun h => ⟨hcov p h.2, h.2⟩⟩
  unfold afterLX
  simp only [e, hsh, hb, hn, hm]

variable [DecidableEq E.Pos]

/-- THE LAX VERIFIER ALONG A SHORT LIST. sh: the wire's own part; wqOf L: the wire with L as its
list of all positions; lst: any list, made of the instance and the verifier's messages. Two tests at
run time guard it. -/
def verifyLXL (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (sh : RoundsQueryLayout lam K P.up.loc.shape P.up.ann) (wqOf : List E.Pos → ProtocolQueryLayout lam K P.up)
    (key : E.Pos → ℕ) (lst : Y → Rho (up P.S) → List E.Pos)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    decide ((lst x ρ).Pairwise (fun a b => key a < key b)) &&
      decide (∀ p ∈ P.extReads x ρ, p ∈ lst x ρ) &&
      afterLX Lf g mk' tst' P (wqOf (lst x ρ)) embS embE depthReq cms x π ρ rts ph

/-- **Its yes is a yes of `verifyLX`**, under the premises on the wire, the key and the two tests
that stand in the statement. -/
theorem verifyLXL_yes (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (wqOf : List E.Pos → ProtocolQueryLayout lam K P.up)
    (hall' : ∀ L, (wqOf L).ext.all = L) (hsh : ∀ L, (wqOf L).sh = wq.sh)
    (hl : ∀ L, (wqOf L).ext.leaf = wq.ext.leaf) (hw : ∀ L, (wqOf L).ext.which = wq.ext.which)
    (hd : ∀ L, (wqOf L).ext.depth = wq.ext.depth) (hb : ∀ L, (wqOf L).ext.build = wq.ext.build)
    (hn : ∀ L, (wqOf L).nOpen = wq.nOpen) (hm : ∀ L, (wqOf L).maxDepth = wq.maxDepth)
    (key : E.Pos → ℕ) (s : wq.ext.all.Pairwise (fun a b => key a < key b))
    (hall : ∀ p, p ∈ wq.ext.all) (htst : ∀ R p, tst (mk R) p = true ↔ p ∈ R)
    (htst' : ∀ R p, tst' (mk' R) p = true ↔ p ∈ R)
    (lst : Y → Rho (up P.S) → List E.Pos)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up)
    (h : verifyLXL Lf g mk' tst' early late t P wq.sh wqOf key lst embS embP xin embE depthReq cms x
      π = true) :
    verifyLX Lf g mk tst early late t P wq embS embP xin embE depthReq cms x π = true := by
  unfold verifyLXL at h
  unfold verifyLX
  cases hc : chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none =>
    rw [hc] at h
    cases h
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    rw [hc] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    show afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph = true
    rw [← afterLX_listed Lf g mk tst mk' tst' P wq (wqOf (lst x ρ)) (hsh _) (hl _) (hw _) (hd _)
      (hb _) (hn _) (hm _) key s hall htst htst' embS embE depthReq cms x π ρ rts ph
      (by rw [hall']; exact h1)
      (fun p hp => by rw [hall']; exact h2 p ((htst _ p).1 hp))]
    exact h3

end TypedOracleCompiler.Run.Thin
