-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstReturns.lean: (B2) OVER THE KEY FILE's FIRST CHAIN's OWN FLAT LIST, AT EVERY
NUMBER, WITH THE NAMED TESTS ON VALUES WRITTEN OUT; from one named premise at one sub-protocol.
Definitions, statements and proofs. Sub-protocols of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

How. As in E2E/KeyShapeFirstWhole.lean: two lists side by side: the chain's flat list, and a list of
pairs: a guard on the shape and a named test on values. `ReturnsV` says (B2) of one sub-protocol and
one pair; where it holds member by member, (B2) holds at every number (`returns_pairs`). No number
of a place is computed.

  `Val`, `vT`, `vOf`: a named test on values; the one that asks nothing; a list's b-th.
  `ReturnsV`, `returnsV_exact`, **`returns_pairs`**: the relation, and the rule.
  **`gvAll₁`**: the first chain's guards, each with its named test: ONE ON THE CLAIMS ON THE KEYS
    (`keysSumB`) at "batt.1.batt"; a letter at the ranges' test; nothing at all others (the three
    sendings, a link's six, "rng.0.rows", the seal).
  `gvAll₁_fst`: its guards are E2E/KeyShapeFirstWhole.lean's `gAll₁`.
  **`Z₁V`**: `Z₁W` at these tests. **`returnsV₁`**: member by member. **`returns_all₁`**: (B2) AT
    EVERY NUMBER.
  `QuietV`, `vals_pairs`, `quietV₁`, **`vals_quiet₁`**: at every sub-protocol without a round the
    named test asks nothing.

Limits.
- ONE NAMED PREMISE, paid nowhere here: (B2) of the ranges' proximity test, at a letter for its
  tests on values. THE PREMISE CAN BE HAD FOR NOTHING: at the test that rejects everything, and at
  the decision's own accept: then (B2) says nothing at that sub-protocol, and all is moved into what
  the frame's rule asks of the values. What it is worth hangs on the test that is laid in for the
  letter.
- Premises on public values: "w.1.send" is there; for `vals_quiet₁`: the ranges' test has a round.


-/
import E2E.KeyShapeFirstWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (Shape Returns ReturnsR)
open VerifiableInference.Desc (Block roundsFit noDigest)
open VerifiableInference.Desc.Key (FirstState Claim lookupsOf lookupLink layRows groupsTold
  rootsBefore rootsAt pieces batchLens batchWhere)
open AtPublicFiles.KeyShape (Pub1 ExactAt gLink link_exact layRows_exactAt gLayRows lookAt gLaid gCaller gHear
  gLayer gCleared)

/-! ## One sub-protocol, one guard, one named test -/

section One
variable {S Cl Sh : Type}

/-- A named test on values. -/
abbrev Val (S : Type) : Type := S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool

/-- The test that asks nothing. -/
def vT : Val S := fun _ _ _ => true

/-- A list's b-th; behind its end: the test that asks nothing. -/
def vOf (vs : List (Val S)) (b : Nat) : Val S := (vs[b]?).getD vT

/-- **(B2) of one sub-protocol and one pair.** -/
def ReturnsV (ft : Nat) (sh : S → Sh) (blk : Block S Cl)
    (x : (Sh → Except String Sh) × Val S) : Prop :=
  ∀ s rs cols t, x.1 (sh s) = .ok t → blk.Fits ft rs cols →
    x.2 s (rs.map noDigest) (blk.shown ft rs cols) = true →
    ∃ s', blk.decide s (rs.map noDigest) (blk.shown ft rs cols) = .ok s'

theorem returnsV_exact {ft : Nat} {sh : S → Sh} {blk : Block S Cl} {g : Sh → Except String Sh}
    (h : ExactAt ft sh blk g) : ReturnsV ft sh blk (g, vT) := fun s rs cols t hg hf _ => by
  obtain ⟨s', e, -⟩ := h s t rs cols hg hf
  exact ⟨s', e⟩

/-- **The rule**: member by member, so at every number. -/
theorem returns_pairs {ft : Nat} {sh : S → Sh} :
    ∀ (bs : List (Block S Cl)) (gv : List ((Sh → Except String Sh) × Val S)),
      List.Forall₂ (ReturnsV ft sh) bs gv → ∀ j : Nat,
        Returns bs ft (ZL sh (gv.map (·.1)) (vOf (gv.map (·.2)))) j
  | _, _, .nil, _ => fun _ hb => by cases hb
  | _, _, .cons (a := b) (b := x) (l₁ := bs) (l₂ := gv) h _, 0 => fun blk hb => by
    obtain rfl : b = blk := Option.some.inj hb
    exact h
  | _, _, .cons (a := b) (b := x) (l₁ := bs) (l₂ := gv) _ ht, j + 1 => fun blk hb =>
    returns_pairs bs gv ht j blk hb

end One

/-! ## The first chain -/

variable (Q : Pub1) (cs : Codes) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (N : H2U.PlaceNums) (vRng : Val FirstState)

/-- The one named test of "batt.1.batt". -/
def vKeys : Val FirstState := fun s _ _ =>
  keysSumB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups s.base.keys

/-- **The first chain's guards, each with its named test on values**, in the order of the flat list.
vRng: a letter: the ranges' test's. -/
def gvAll₁ : List ((Sh₁B → Except String Sh₁B) × Val FirstState) :=
  (gIdx Q pieces (groupsTold told 0 (rootsAt D 0)), vT) ::
    [(gMsg Q pieces (groupsTold told (rootsBefore D 2) (rootsAt D 2)), vT)] ++
    ((lookupsOf Q.one).zipIdx.flatMap fun x => (gLink Q x.2).map fun g => (g, vT)) ++
    [(gLayRows Q, vT), (gRng Q N, vRng), (gBatt Q cs pieces (sentAt D), vKeys Q),
      (gSendW Q pieces (groupsW D told), vT)] ++
    [(gSealB, vT)]

/-- Its guards are the chain's. -/
theorem gvAll₁_fst : (gvAll₁ Q cs D told N vRng).map (·.1) = gAll₁ Q cs D told N := by
  unfold gvAll₁ gAll₁
  have e : ∀ l : List (Sh₁B → Except String Sh₁B),
      l.map ((fun x : (Sh₁B → Except String Sh₁B) × Val FirstState => x.1) ∘
        fun g => (g, vT)) = l := fun l => by
    have h : ((fun x : (Sh₁B → Except String Sh₁B) × Val FirstState => x.1) ∘
        fun g => (g, vT)) = id := rfl
    rw [h, List.map_id]
  simp only [List.map_flatMap, List.map_cons, List.map_map, List.map_append, List.map_nil, e]

/-- **The letters of the cut for the first chain, with its named tests on values written out.** -/
def Z₁V : Shape FirstState :=
  Z₁W Q cs D told N (vOf ((gvAll₁ Q cs D told N vRng).map (·.2)))

/-- **Member by member.** -/
theorem returnsV₁ (ft : Nat) (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hRng : ReturnsV ft (sh₁B Q cs) (H2K.JointK.rngEntry Q.one N) (gRng Q N, vRng)) :
    List.Forall₂ (ReturnsV ft (sh₁B Q cs)) (flat₁ Q D told N) (gvAll₁ Q cs D told N vRng) := by
  rw [flat₁_whole Q D told N bw hw]
  unfold gvAll₁
  refine List.rel_append (List.rel_append (List.rel_append (.cons ?_ (.cons ?_ .nil)) ?_)
    (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))) (.cons ?_ .nil)
  · intro s rs cols t hg hF hv
    exact idx_returns (Cl := Claim) Q _ pieces _ rs _ hF.1 s t hg rfl
  · intro s rs cols t hg hF hv
    exact msg_returns (Cl := Claim) Q _ pieces _ rs _ hF.1 s t hg rfl
  · refine pairs_flatMap _ _ _ fun lk hlk => ?_
    rw [look_at Q hlk]
    refine pairs_of_get _ _ (by rw [List.length_map]; rfl) fun k blk y hb hy => ?_
    rw [List.getElem?_map] at hy
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact returnsV_exact (link_exact Q _ lk.2 ft k blk g hb hg)
  · exact returnsV_exact (layRows_exactAt Q _ ft)
  · exact hRng
  · intro s rs cols t hg hF hv
    have e : (VerifiableInference.Desc.Key.batchTableRows (Cl := Claim) keysAt Q.one pieces
        (sentAt D)).asBare.rounds =
        VerifiableInference.Desc.K13.battRounds (batchWhere Q.one pieces (sentAt D)) :=
      List.append_nil _
    exact batt_returns (Cl := Claim) Q cs pieces (sentAt D) s t hg hv rs (e ▸ hF.1) _
  · intro s rs cols t hg hF hv
    exact sendW_returns (Cl := Claim) Q cs pieces (sentAt D) (groupsW D told) bw hw rs _ hF.1 s t
      hg rfl
  · intro s rs cols t hg _ _
    exact (seal_both (Cl := Claim) Q cs pieces [] (rs.map noDigest)
      (Block.shown ft (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).last.asBare rs
        cols)).2 s t hg rfl

/-- **(B2) AT EVERY NUMBER OF THE FIRST CHAIN's OWN FLAT LIST.** -/
theorem returns_all₁ (ft : Nat) (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hRng : ReturnsV ft (sh₁B Q cs) (H2K.JointK.rngEntry Q.one N) (gRng Q N, vRng)) (j : Nat) :
    Returns (flat₁ Q D told N) ft (Z₁V Q cs D told N vRng) j := by
  have h := returns_pairs _ _ (returnsV₁ Q cs D told N vRng ft bw hw hRng) j
  rw [gvAll₁_fst] at h
  exact h

/-! ## The named tests at the sub-protocols without a round -/

/-- Of one sub-protocol and one pair: where the sub-protocol has no round, the pair's test asks
nothing. -/
def QuietV {S Cl Sh : Type} (blk : Block S Cl) (x : (Sh → Except String Sh) × Val S) : Prop :=
  blk.rounds = [] → x.2 = vT

/-- The rule: member by member, so at every number. -/
theorem vals_pairs {S Cl Sh : Type} :
    ∀ (bs : List (Block S Cl)) (gv : List ((Sh → Except String Sh) × Val S)),
      List.Forall₂ QuietV bs gv → ∀ (j : Nat) (blk : Block S Cl), bs[j]? = some blk →
        blk.rounds = [] → vOf (gv.map (·.2)) j = vT
  | _, _, .nil, _, _, hb, _ => by cases hb
  | _, _, .cons (a := b) (b := x) (l₁ := bs) (l₂ := gv) h _, 0, blk, hb, hr => by
    obtain rfl : b = blk := Option.some.inj hb
    exact h hr
  | _, _, .cons (a := b) (b := x) (l₁ := bs) (l₂ := gv) _ ht, j + 1, blk, hb, hr =>
    vals_pairs bs gv ht j blk hb hr

/-- Member by member. hR: the ranges' test has a round. -/
theorem quietV₁ (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hR : (H2K.JointK.rngEntry Q.one N).rounds ≠ []) :
    List.Forall₂ QuietV (flat₁ Q D told N) (gvAll₁ Q cs D told N vRng) := by
  rw [flat₁_whole Q D told N bw hw]
  unfold gvAll₁
  refine List.rel_append (List.rel_append (List.rel_append (.cons ?_ (.cons ?_ .nil)) ?_)
    (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))) (.cons ?_ .nil)
  · exact fun h => by cases h
  · exact fun h => by cases h
  · refine pairs_flatMap _ _ _ fun x _ => ?_
    refine pairs_of_get _ _ (by rw [List.length_map]; rfl) fun k blk y _ hy _ => ?_
    rw [List.getElem?_map] at hy
    obtain ⟨g, -, rfl⟩ := Option.map_eq_some_iff.1 hy
    rfl
  · exact fun _ => rfl
  · exact fun h => absurd h hR
  · exact fun h => by cases h
  · unfold sendWAt VerifiableInference.Desc.Key.sendW at hw
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
    exact fun h => by cases h
  · exact fun _ => rfl

/-- **AT EVERY SUB-PROTOCOL OF THE FIRST CHAIN THAT HAS NO ROUND THE NAMED TEST ON VALUES ASKS
NOTHING.** -/
theorem vals_quiet₁ (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hR : (H2K.JointK.rngEntry Q.one N).rounds ≠ []) (j : Nat) (blk : Block FirstState Claim)
    (hb : (flat₁ Q D told N)[j]? = some blk) (hr : blk.rounds = []) (s : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (Z₁V Q cs D told N vRng).vals j s rs gs = true := by
  show vOf ((gvAll₁ Q cs D told N vRng).map (·.2)) j s rs gs = true
  rw [vals_pairs _ _ (quietV₁ Q cs D told N vRng bw hw hR) j blk hb hr]
  rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.returnsV_exact
#print axioms AtPublicFiles.AtFiles.returns_pairs
#print axioms AtPublicFiles.AtFiles.gvAll₁_fst
#print axioms AtPublicFiles.AtFiles.returnsV₁
#print axioms AtPublicFiles.AtFiles.returns_all₁
#print axioms AtPublicFiles.AtFiles.vals_pairs
#print axioms AtPublicFiles.AtFiles.quietV₁
#print axioms AtPublicFiles.AtFiles.vals_quiet₁
