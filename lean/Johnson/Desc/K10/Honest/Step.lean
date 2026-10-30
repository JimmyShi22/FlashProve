-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Step.lean: THE STEP OF THE BLOCK OF THE CLOSING OF A SEGMENT SAYS YES: the two
tests that a block's step asks in front of the decision (`Block.step`, Johnson/Desc/Block.lean: "the
rounds", "the columns") pass at every list of 2 + k rounds of the kind's shape; with
Johnson/Desc/K10/Honest/Base.lean and BaseB.lean the whole step says yes. Theorems on the verifier's
own text. It names no frame of an honest side.

  `round_fit`, `rounds_fit`   "the rounds": a round of the shape fits its declared round: it shows just
                    the items that its entry cuts, drew as many of each sort as the entry says, and
                    no drawn element is marked as never 0
  `groups_nil`      "the columns": the kind's rounds open no tree and no stored table: none is owed
  `shapedAll_noDigest`, `batDraw_noDigest`   the shape is kept where the sealed digest is taken away,
                    as the step does in front of the decision
  `step_of_decide`  so the step says yes, and takes no column, where the decision says yes at the
                    rounds without the digest
  `close_step_all`, `close_step_of`   THE STEP SAYS YES at every such list of rounds and every list of
                    columns: from `CloseBase`; from `closeBaseB P s = true`

Limits. Of the kind's block at its own record: the first chain runs it lifted, wrapped and guarded:
Johnson/Desc/K10/Honest/AtS.lean. The block's test on the plan (`planOk`: 1 ≤ k and h ≤ k), that it has
a list of oracle messages for each round (`shaped`) and what must have been sent before (`before`) are
not read by the step; the verifier asks them first, among the file's tests on the plan
(`FileDescription.planOk`, Johnson/Desc/Block.lean): not spoken of. Whether the record that an honest run
leaves in front of the block meets the facts is not said. Nothing on soundness, completeness or hiding
of the protocol.

-/
import Johnson.Desc.K10.Honest.BaseB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- A round of the shape fits a declared round whose entry sends n elements, no answer and no root,
draws one element, none marked as never 0, and has a name that the format knows, of another kind
than a round of seeds. -/
theorem round_fit {e : Fmt.Entry} {n : Nat} {r : Fmt.RoundView} (h1 : e.answers = 0) (h2 : e.roots = 0)
    (h3 : e.msg = 24 * n) (h4 : e.drawE = 1) (h5 : e.poss = 0) (h6 : e.trits = 0)
    (h7 : e.drawNZ = 0) {k : Fmt.Kind} (h8 : Fmt.kindOf e.name = some k) (h9 : k ≠ .seeds)
    (hs : Shaped n r)
    (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) :
    roundsFit ({ entry := e } :: ds) (r :: rs) = roundsFit ds rs := by
  obtain ⟨⟨ys, hv, hl⟩, ⟨t, ht⟩, hp, hq⟩ := hs
  have i1 : r.vals.map itemOf = List.replicate n Fmt.Item.e := by
    rw [hv, List.map_map, ← hl]
    exact List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hb
      rfl⟩
  have i2 : (({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root)) =
      List.replicate n Fmt.Item.e := by
    show (e.cut.filter (· != .root)) = _
    unfold Fmt.Entry.cut
    rw [h1, h2, h3]
    simp
  have i3 : drawsMarkedNonzeroHaveNonzeroWords { entry := e } r = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    show ((Fmt.kindOf e.name).any _) = true
    rw [h8]
    show (((Fmt.dsElems e k).zip r.drawn.elems).all _) = true
    unfold Fmt.dsElems
    rw [if_neg h9, h4, h7, ht]
    rfl
  rw [roundsFit, i1, i2, i3, ht, hp, hq]
  simp [h4, h5, h6]

theorem kind_bat : Fmt.kindOf "BAT" = some .elems := by decide
theorem kind_eps : Fmt.kindOf "FOLD epsilon" = some .join := by decide
theorem kind_round : Fmt.kindOf "FOLD round" = some .elems := by decide

/-- **"The rounds"**: 2 + k rounds of the kind's shape fit the kind's declared rounds. -/
theorem rounds_fit {Cl : Type} (P : Par) (rs : List Fmt.RoundView) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) : roundsFit ((kind (Cl := Cl)) P).rounds rs = true := by
  match rs, hl, hs with
  | rB :: rE :: rR, hl, ⟨t1, t2, t3⟩ =>
    show roundsFit ((entries P).map fun e => ({ entry := e } : Fmt.DeclaredRound)) _ = true
    rw [entries_eq, List.map_cons, List.map_cons,
      round_fit (e := eBat P) (n := 0) rfl rfl rfl rfl rfl rfl rfl kind_bat (by decide) t1,
      round_fit (e := eEps P) (n := 1) rfl rfl rfl rfl rfl rfl rfl kind_eps (by decide) t2,
      List.map_replicate]
    have hlen : rR.length = P.k := by simp at hl; omega
    clear hl t1 t2
    generalize P.k = k at hlen
    induction k generalizing rR with
    | zero =>
      obtain rfl := List.eq_nil_of_length_eq_zero hlen
      rfl
    | succ k ih =>
      match rR, hlen, t3 with
      | r :: rR', hlen, t3 =>
        rw [List.replicate_succ,
          round_fit (e := eRound P) (n := 2) rfl rfl rfl rfl rfl rfl rfl kind_round (by decide)
            (t3 r List.mem_cons_self)]
        exact ih rR' (fun q hq => t3 q (List.mem_cons_of_mem _ hq)) (Nat.succ.inj hlen)

/-- **"The columns"**: rounds that open nothing are owed no column. -/
theorem groups_nil (ft : Nat) : ∀ (es : List Fmt.Entry) (Rs : List Fmt.Drawn),
    groupsOf ft (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) Rs = []
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: es, _ :: Rs => by
    show [] ++ [] ++ groupsOf ft (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) Rs = []
    rw [groups_nil ft es Rs]
    rfl

theorem shaped_noDigest {n : Nat} {r : Fmt.RoundView} (h : Shaped n r) : Shaped n (noDigest r) := h

theorem shapedAll_noDigest : ∀ {rs : List Fmt.RoundView}, ShapedAll rs → ShapedAll (rs.map noDigest)
  | _ :: _ :: _, ⟨a, b, c⟩ => ⟨shaped_noDigest a, shaped_noDigest b, fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact shaped_noDigest (c q hq)⟩

theorem batDraw_noDigest (rs : List Fmt.RoundView) : batDraw (rs.map noDigest) = batDraw rs := by
  cases rs <;> rfl

/-- **The step says yes, and takes no column, where the decision says yes at the rounds without the
digest.** -/
theorem step_of_decide {Cl : Type} (P : Par) (ft : Nat) (s s' : Rec) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hl : rs.length = 2 + P.k) (hs : ShapedAll rs)
    (h : ((kind (Cl := Cl)) P).decide s (rs.map noDigest) [] = .ok s') :
    ((kind (Cl := Cl)) P).step ft s rs cols = .ok (s', 0) := by
  have g : groupsOf ft ((kind (Cl := Cl)) P).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (entries P) _
  unfold Block.step
  rw [rounds_fit P rs hl hs, g]
  show (((kind (Cl := Cl)) P).decide s (rs.map noDigest) []).bind _ = _
  rw [h]
  rfl

/-- **FROM FACTS THAT NAME NONE OF THE BLOCK's CHALLENGES ITS STEP SAYS YES** at every list of 2 + k
rounds of the kind's shape and every list of columns. -/
theorem close_step_all {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) : ∃ s', ((kind (Cl := Cl)) P).step ft s rs cols = .ok (s', 0) := by
  obtain ⟨s', h⟩ := close_yes_all (Cl := Cl) H (rs.map noDigest) [] (by rw [List.length_map, hl])
    (shapedAll_noDigest hs)
  exact ⟨s', step_of_decide P ft s s' rs cols hl hs h⟩

/-- **The same from the test with code.** -/
theorem close_step_of {Cl : Type} {P : Par} {s : Rec} (h : closeBaseB P s = true) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 2 + P.k) (hs : ShapedAll rs) :
    ∃ s', ((kind (Cl := Cl)) P).step ft s rs cols = .ok (s', 0) := by
  obtain ⟨D, H⟩ := closeBase_of h
  exact close_step_all H ft rs cols hl hs

namespace Toy

/-- `close_step_of`, called at BaseB.lean's member. -/
theorem all_steps (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 4)
    (hs : ShapedAll rs) : ∃ s', ((kind (Cl := Unit)) P).step ft s rs cols = .ok (s', 0) :=
  close_step_of base_member ft rs cols hl hs

/-- A second road to one such yes, and to "no column": Lean's kernel evaluates the step itself at the
toy's rounds. -/
theorem step_yes : (((kind (Cl := Unit)) P).step 0 s MeansToys.rs0 []).toOption.map (·.2) = some 0 := by
  decide +kernel

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.rounds_fit
#print axioms ProofFile.Honest.K10.YesFree.step_of_decide
#print axioms ProofFile.Honest.K10.YesFree.close_step_all
#print axioms ProofFile.Honest.K10.YesFree.close_step_of
#print axioms ProofFile.Honest.K10.YesFree.Toy.all_steps
#print axioms ProofFile.Honest.K10.YesFree.Toy.step_yes
