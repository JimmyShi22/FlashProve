-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyKeysKeeps.lean: ALONG THE KEY FILE's FIRST CHAIN, UP TO AND WITH THE RANGES' PROXIMITY TEST,
THE CLAIMS ON THE LOOKUPS' KEYS THAT LIE IN THE STATE ARE THE ONES THAT THE LOOKUPS' OWN TEXT MAKES,
EACH AT ITS OWN LOOKUP's NUMBER. From the sub-protocols' own accepts, at all values. Definitions,
statements and proofs. Steps of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `KeysAt one n s`: the state holds n lists of claims on keys, and list number j is a value of
    `K3.keyClaims` (Johnson/Desc/First/Look/K3Key.lean) at lookup number j.
  `keysAt_same`, `keysAt_push`: it is kept where the lists stay, and where one such list is laid
    behind.
  `fold_cons_d`: a fold's first step, as an accept of the member's decision.
  `claims_keys`: a link's three runs of claims leave the lists (the proof goes as
    E2E/KeyMarksKeeps.lean's `claims_keeps`).
  **`link_keys`**: a fold over the six sub-protocols of lookup number i's link: from i lists to i +
    1.
  `links_keys`: over all links.
  **`keys_of_front`**: over all that stands in front of "batt.1.batt": from none to one for each
    lookup.

By what. The library's `callerD_law`, `layerD_law` (Johnson/RunOne/Law/AtKeyD.lean), `link_flat`
(Law/LinkSeats.lean), `lay_ok`, `after_ok`, `clear_ok` (Johnson/RunOne/KeyTen.lean), `block_law`;
`idx_plain`, `msg_plain` (E2E/KeyMarksWalk.lean); `layRows_says`
  (Johnson/Desc/K12/Honest/Shape/TestMarksAtRanges.lean);
`ranges_inv` (E2E/KeyShapeRanges.lean): CALLED.

Limits.
- The layer of lookup number i lays its list behind whatever lies there. That i lists lie there is
  carried by `KeysAt` itself along the folds; the caller's own test on that count is not spent.
- `keys_of_front`'s premise on the statement's rows is asked because `idx_plain` and `msg_plain` are
  stated so: it feeds these two laws' own premises; what is spent of them for `KeysAt` is "the
  lookups' part of the state stays".
- FORM AND ORIGIN ALONE: that a claim holds of anything is not touched.


-/
import E2E.KeyMarksThr
import E2E.KeyPileAccepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.K3.KeyLaw (bindB runIn_ok bindX namedX block_law)
open VerifiableInference.Desc.Ground.Sh (stPlainB)
open Johnson.RunOne.Law.AtKeyD (callerD_law layerD_law)
open Johnson.RunOne.Law.LinkSeats (link_flat)
open Johnson.RunOne.KeyRows1 (lay_ok after_ok clear_ok)
open H2K.JointK (keyFirstPre rngEntry)
open AtPublicFiles.KeyLookup (idx_plain msg_plain)
open ProofFile.Honest.Sh (layRows_says)

/-- **n lists of claims on keys lie in the state, each made by the lookups' own text at its own
lookup's number.** -/
def KeysAt (one : Params.OneTime) (n : ℕ) (s : FirstState) : Prop :=
  s.base.keys.length = n ∧ ∀ (j : ℕ) (ks : List Lkp.Keys), s.base.keys[j]? = some ks →
    ∃ x F home g, (lookupsOf one)[j]? = some x ∧ keyClaims x F home g = some ks

theorem keysAt_same {one : Params.OneTime} {n : ℕ} {s s' : FirstState}
    (e : s'.base.keys = s.base.keys) (h : KeysAt one n s) : KeysAt one n s' :=
  ⟨by rw [e]; exact h.1, fun j ks hj => h.2 j ks (by rw [← e]; exact hj)⟩

theorem keysAt_push {one : Params.OneTime} {n : ℕ} {s s' : FirstState} {x : Lookup} {F : Fork}
    {home : Array Slot} {g : HeardG} {ks : List Lkp.Keys} (hx : (lookupsOf one)[n]? = some x)
    (hk : keyClaims x F home g = some ks) (e : s'.base.keys = s.base.keys ++ [ks])
    (h : KeysAt one n s) : KeysAt one (n + 1) s' := by
  refine ⟨by rw [e, List.length_append, h.1, List.length_singleton], fun j ks' hj => ?_⟩
  rw [e] at hj
  by_cases c : j < s.base.keys.length
  · rw [List.getElem?_append_left c] at hj
    exact h.2 j ks' hj
  · have c' : s.base.keys.length ≤ j := Nat.le_of_not_lt c
    rw [List.getElem?_append_right c'] at hj
    have hz : j - s.base.keys.length = 0 := by
      by_contra hne
      have h1 : [ks].length ≤ j - s.base.keys.length := by
        show 1 ≤ _
        omega
      rw [List.getElem?_eq_none h1] at hj
      cases hj
    rw [hz] at hj
    have e1 : ks = ks' := Option.some.inj hj
    have e2 : j = n := by
      have := h.1
      omega
    rw [e2, ← e1]
    exact ⟨x, F, home, g, hx, hk⟩

/-- A fold's first step, as an accept of the member's decision. -/
theorem fold_cons_d {ft : ℕ} {b : Block FirstState Key.Claim}
    {l : List (Block FirstState Key.Claim)} {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {r : FirstState × List Fmt.RoundView × List OpenedColumn} (h : foldBlocks ft (b :: l) s rs cols = .ok r) :
    ∃ s' rs₁ gs₁ rs₂ cols₂, b.decide s rs₁ gs₁ = .ok s' ∧
      foldBlocks ft l s' rs₂ cols₂ = .ok r := by
  obtain ⟨-, s', k, st, rest⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨rs₁, gs₁, hd⟩ := ChainEnd.step_decide ft b s s' _ cols k st
  exact ⟨s', rs₁, gs₁, _, _, hd, rest⟩

/-- The link's three runs of claims leave the lists of claims on keys. -/
theorem claims_keys {b0 : Block FirstState Key.Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {cls : List Key.Claim}
    (h : claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")] s = .ok (cls, s')) :
    s'.base.keys = s.base.keys := by
  unfold claimsIn claimsInBy at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  obtain ⟨x2, h, h3⟩ := bindB h
  obtain ⟨x1, h, h2⟩ := bindB h
  obtain ⟨x0, h0, h1⟩ := bindB h
  cases h0
  obtain ⟨z1, r1, rfl⟩ := runIn_ok (o := (1, "objects")) rfl h1
  obtain ⟨z2, r2, rfl⟩ := runIn_ok (o := (1, "planes")) rfl h2
  obtain ⟨z3, r3, e3⟩ := runIn_ok (o := (1, "guests")) rfl h3
  obtain ⟨F1, a1, r1⟩ := bindX r1
  obtain ⟨g1, a2, r1⟩ := bindX r1
  cases r1
  obtain ⟨F2, b1, r2⟩ := bindX r2
  obtain ⟨g2, b2, r2⟩ := bindX r2
  obtain ⟨_, -, r2⟩ := bindX r2
  obtain ⟨y, b4, r2⟩ := bindX r2
  obtain ⟨l, b5, r2⟩ := bindX r2
  cases r2
  have h9 := namedX r3
  cases h9
  obtain ⟨-, rfl⟩ := Prod.mk.inj e3
  rfl

/-- **A fold over the six sub-protocols of lookup number i's link.** -/
theorem link_keys (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) (ft : ℕ)
    {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {r : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (lookupLink one set i x).blocksInOrder s rs cols = .ok r)
    (hx : (lookupsOf one)[i]? = some x) (hA : KeysAt one i s) : KeysAt one (i + 1) r.1 := by
  obtain ⟨c0, c4, c5, hf, h0, h4, h5⟩ := link_flat one set i x
  rw [hf] at h
  obtain ⟨s1, _, _, _, _, d0, h⟩ := fold_cons_d h
  obtain ⟨s2, _, _, _, _, d1, h⟩ := fold_cons_d h
  obtain ⟨s3, _, _, _, _, d2, h⟩ := fold_cons_d h
  obtain ⟨s4, _, _, _, _, d3, h⟩ := fold_cons_d h
  obtain ⟨s5, _, _, _, _, d4, h⟩ := fold_cons_d h
  obtain ⟨s6, _, _, _, _, d5, h⟩ := fold_cons_d h
  have e7 : s6 = r.1 := congrArg Prod.fst (Except.ok.inj h)
  rw [h0] at d0
  rw [h4] at d4
  rw [h5] at d5
  have k1 : s1.base.keys = s.base.keys := by rw [lay_ok one set i x s s1 d0]
  have k2 : s2.base.keys = s1.base.keys := by
    obtain ⟨-, -, o, k, -, -, -, e⟩ := callerD_law d1
    subst e
    rfl
  have k3 : s3.base.keys = s2.base.keys := by
    obtain ⟨F, g, G, es, -, -, -, -, -, e⟩ := block_law _ _ _ _ _ d2
    subst e
    rfl
  obtain ⟨cls, t, F', g', rows, keys, c1, -, -, -, hk, e4⟩ := layerD_law d3
  have k4 : s4.base.keys = s3.base.keys ++ [keys] := by
    subst e4
    show t.base.keys ++ [keys] = _
    rw [claims_keys c1]
  have k5 : s5.base.keys = s4.base.keys := by rw [after_ok one set i x s4 s5 d4]
  have k6 : s6.base.keys = s5.base.keys := by
    rw [clear_ok one set i x s5 s6 d5]
    rfl
  rw [← e7]
  exact keysAt_push hx hk (by rw [k6, k5, k4, k3, k2, k1]) hA

/-- Over all links, from lookup number n on. -/
theorem links_keys (one : Params.OneTime) (set : Params.Setting) (ft : ℕ) :
    ∀ (L : List Lookup) (n : ℕ) (s : FirstState) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (r : FirstState × List Fmt.RoundView × List OpenedColumn),
      (∀ j x, L[j]? = some x → (lookupsOf one)[n + j]? = some x) →
      foldBlocks ft (((L.zipIdx n).map fun x => lookupLink one set x.2 x.1).flatMap Link.blocksInOrder)
        s rs cols = .ok r → KeysAt one n s → KeysAt one (n + L.length) r.1
  | [], n, s, rs, cols, r, _, h, hA => by
    have e : s = r.1 := congrArg Prod.fst (Except.ok.inj h)
    rw [← e]
    exact hA
  | x :: L, n, s, rs, cols, r, hx, h, hA => by
    rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons] at h
    obtain ⟨t, rs', cols', f1, f2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
    have a := link_keys one set n x ft f1 (hx 0 x rfl) hA
    have b := links_keys one set ft L (n + 1) t rs' cols' r (fun j y hy => by
      have q := hx (j + 1) y (by rw [List.getElem?_cons_succ]; exact hy)
      rwa [show n + (j + 1) = n + 1 + j by omega] at q) f2 a
    rwa [List.length_cons, show n + (L.length + 1) = n + 1 + L.length by omega]

/-- **OVER ALL THAT STANDS IN FRONT OF "batt.1.batt".** -/
theorem keys_of_front (one : Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Params.Setting) (N : H2U.PlaceNums) (ft : ℕ) {s : FirstState} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {r : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (keyFirstPre one D told set N ++ [rngEntry one N]) s rs cols = .ok r)
    (hp : stPlainB s.d.st = true) (hA : KeysAt one 0 s) :
    KeysAt one (lookupsOf one).length r.1 := by
  obtain ⟨s15, rs1, c1, f1, f2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
  unfold keyFirstPre at f1
  obtain ⟨s14, rs2, c2, g1, g2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 f1
  obtain ⟨s2, rs3, c3, k1, k2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 g1
  have k1' : foldBlocks ft [(firstChain one D told set N).first.asBare,
      (sendOwnMessage (Cl := Key.Claim) one pieces
        (groupsTold told (rootsBefore D 2) (rootsAt D 2))).asBare] s rs cols =
      .ok (s2, rs3, c3) := k1
  obtain ⟨a1, _, _, _, _, d0, k1'⟩ := fold_cons_d k1'
  obtain ⟨a2, _, _, _, _, d1, k1'⟩ := fold_cons_d k1'
  have e2 : a2 = s2 := congrArg Prod.fst (Except.ok.inj k1')
  obtain ⟨p1, b1⟩ := idx_plain (one := one) (N := pieces) d0 hp
  obtain ⟨-, b2⟩ := msg_plain (one := one) (N := pieces) d1 p1
  have A2 : KeysAt one 0 s2 := by
    rw [← e2]
    exact keysAt_same (by rw [b2, b1]) hA
  have k2' : foldBlocks ft ((((lookupsOf one).zipIdx 0).map fun x =>
      lookupLink one set x.2 x.1).flatMap Link.blocksInOrder) s2 rs3 c3 = .ok (s14, rs2, c2) := k2
  have A14 := links_keys one set ft (lookupsOf one) 0 s2 rs3 c3 _
    (fun j x hj => by rwa [Nat.zero_add]) k2' A2
  rw [Nat.zero_add] at A14
  obtain ⟨a15, _, _, _, _, d14, g2⟩ := fold_cons_d g2
  have e15 : a15 = s15 := congrArg Prod.fst (Except.ok.inj g2)
  obtain ⟨-, d, -, q15⟩ := layRows_says (one := one) d14
  have A15 : KeysAt one (lookupsOf one).length s15 := by
    rw [← e15]
    exact keysAt_same (by subst q15; rfl) A14
  obtain ⟨a16, _, _, _, _, d15, f2⟩ := fold_cons_d f2
  have e16 : a16 = r.1 := congrArg Prod.fst (Except.ok.inj f2)
  obtain ⟨tE, -, q16⟩ := ranges_inv one N _ _ _ _ d15
  rw [← e16]
  exact keysAt_same (by subst q16; rfl) A15

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keysAt_same
#print axioms AtPublicFiles.AtFiles.keysAt_push
#print axioms AtPublicFiles.AtFiles.fold_cons_d
#print axioms AtPublicFiles.AtFiles.claims_keys
#print axioms AtPublicFiles.AtFiles.link_keys
#print axioms AtPublicFiles.AtFiles.links_keys
#print axioms AtPublicFiles.AtFiles.keys_of_front
