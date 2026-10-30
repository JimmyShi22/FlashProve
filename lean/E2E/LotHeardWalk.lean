-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHeardWalk.lean: for HeardOfFold: ALONG THE KEY FILE's FIRST CHAIN, UP TO AND WITH THE RANGES'
PROXIMITY TEST, THE CLAIMS ON THE LOOKUPS' KEYS THAT LIE IN THE STATE ARE MADE OF WHAT THE VERIFIER's OWN HEARING HEARD ON
JUST THE LOOKUP's OWN ROUNDS OF THE LIST THAT THE FOLD WAS HANDED. From the sub-protocols' own accepts, at all values.
Steps of the verifier's: nothing is shown of any prover.

  step_decide_r, fold_cons_r, fold_cons_q   a fold's first step, with the rounds that the member is shown and the
                  rounds left; at a member without a round
  claims_heard    a link's three runs of claims leave what was heard
  link_flat_r     the link's six sub-protocols; five have no round
  lenOf, HeardOn  a lookup's number of rounds; «these claims are keyClaims of a hearing on the first lenOf rounds of rs»
  link_heard      a fold over the six sub-protocols of a link
  pre_two         at two lookups: what stands in front of the ranges' test, as a list
  front_heard     over all that stands in front of "batt.1.batt", at two lookups

After: IOP's E2E/KeyKeysKeeps.lean (link_keys, keys_of_front): the same walk, with the rounds carried.

Limits. Form and origin alone: that a claim holds of anything is not touched. Nothing on soundness, completeness,
hiding or binding.
-/
import E2E.KeyKeysKeeps
import E2E.LotHeardText

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH.Lots
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.K3.KeyLaw (bindB runIn_ok bindX namedX block_law hearE)
open VerifiableInference.Desc.Ground.Sh (stPlainB)
open Johnson.RunOne.Law.AtKeyD (callerD_law layerD_law)
open Johnson.RunOne.KeyRows1 (lay_ok after_ok clear_ok)
open H2K.JointK (keyFirstPre rngEntry)
open AtPublicFiles.KeyLookup (idx_plain msg_plain)
open ProofFile.Honest.Sh (layRows_says)
open AtPublicFiles.AtFiles (ranges_inv)

section
variable {S Cl : Type}

/-- A step that says yes: the member's decision says yes on the rounds without their sealed digests. -/
theorem step_decide_r (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ gs', b.decide s (rs.map noDigest) gs' = .ok s' := by
  unfold Block.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ _ _ _ t ht
        injection h with h
        injection h with h1 _
        subst h1
        exact ⟨_, ht⟩

/-- A fold's first step, with the rounds. -/
theorem fold_cons_r {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (b :: l) s rs cols = .ok r) :
    ∃ s' gs₁ cols₂, b.decide s ((rs.take b.rounds.length).map noDigest) gs₁ = .ok s' ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) cols₂ = .ok r := by
  obtain ⟨-, s', k, st, rest⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨gs₁, hd⟩ := step_decide_r ft b s s' _ cols k st
  exact ⟨s', gs₁, _, hd, rest⟩

/-- The same at a member without a round. -/
theorem fold_cons_q {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn} (hq : b.rounds = [])
    (h : foldBlocks ft (b :: l) s rs cols = .ok r) :
    ∃ s' rs₁ gs₁ cols₂, b.decide s rs₁ gs₁ = .ok s' ∧ foldBlocks ft l s' rs cols₂ = .ok r := by
  obtain ⟨s', gs₁, cols₂, hd, rest⟩ := fold_cons_r h
  rw [hq, List.length_nil, List.drop_zero] at rest
  exact ⟨s', _, gs₁, cols₂, hd, rest⟩

end

/-- The link's three runs of claims leave what was heard. -/
theorem claims_heard {b0 : Block FirstState Key.Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {cls : List Key.Claim}
    (h : claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")] s = .ok (cls, s')) :
    s'.base.heard = s.base.heard := by
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

/-- The link's flat list: six sub-protocols, what each decides, and that five have no round. -/
theorem link_flat_r (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) :
    ∃ c0 c4 c5 : Block FirstState Key.Claim,
      (lookupLink one set i x).blocksInOrder =
        [c0, caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x),
          layer one set i x
            (claimsIn [caller one i x,
                lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)]
              [(1, "objects"), (1, "planes"), (1, "guests")]), c4, c5] ∧
      (∀ s rs gs, c0.decide s rs gs = (lookupLink one set i x).lay s) ∧
      (∀ s rs gs, c4.decide s rs gs =
        afterIn [caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)] []
            s) ∧
      (∀ s rs gs, c5.decide s rs gs = (lookupLink one set i x).clear s) ∧
      c0.rounds = [] ∧ (caller one i x : Block FirstState Key.Claim).rounds = [] ∧
      (layer one set i x
            (claimsIn [caller one i x,
                lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)]
              [(1, "objects"), (1, "planes"), (1, "guests")])).rounds = [] ∧
      c4.rounds = [] ∧ c5.rounds = [] :=
  ⟨_, _, _, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A lookup's number of rounds. -/
def lenOf (set : Params.Setting) (i : ℕ) (x : Lookup) : ℕ :=
  (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x) :
    Block FirstState Key.Claim).rounds.length

/-- **These claims on keys are the lookups' own text's, of a hearing on the first rounds of rs.** -/
def HeardOn (set : Params.Setting) (i : ℕ) (x : Lookup) (rs : List Fmt.RoundView)
    (keys : List Lkp.Keys) : Prop :=
  ∃ F home g es F₀ G, keyClaims x F home g = some keys ∧
    hearE (lookupPlace set i x).face es F₀ ((rs.take (lenOf set i x)).map noDigest) = some (g, G)

/-- **A fold over the six sub-protocols of lookup number i's link.** -/
theorem link_heard (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) (ft : ℕ)
    {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {r : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (lookupLink one set i x).blocksInOrder s rs cols = .ok r) :
    ∃ keys, HeardOn set i x rs keys ∧ r.1.base.keys = s.base.keys ++ [keys] ∧
      r.2.1 = rs.drop (lenOf set i x) := by
  obtain ⟨c0, c4, c5, hf, h0, h4, h5, q0, q1, q3, q4, q5⟩ := link_flat_r one set i x
  rw [hf] at h
  obtain ⟨s1, _, _, _, d0, h⟩ := fold_cons_q q0 h
  obtain ⟨s2, _, _, _, d1, h⟩ := fold_cons_q q1 h
  obtain ⟨s3, _, _, d2, h⟩ := fold_cons_r h
  obtain ⟨s4, _, _, _, d3, h⟩ := fold_cons_q q3 h
  obtain ⟨s5, _, _, _, d4, h⟩ := fold_cons_q q4 h
  obtain ⟨s6, _, _, _, d5, h⟩ := fold_cons_q q5 h
  have e7 := Except.ok.inj h
  rw [h0] at d0
  rw [h4] at d4
  rw [h5] at d5
  have k1 : s1.base.keys = s.base.keys := by rw [lay_ok one set i x s s1 d0]
  have k2 : s2.base.keys = s1.base.keys := by
    obtain ⟨-, -, o, k, -, -, -, e⟩ := callerD_law d1
    subst e
    rfl
  obtain ⟨F, g, G, es, -, -, -, -, hh, e3⟩ := block_law _ _ _ _ _ d2
  have k3 : s3.base.keys = s2.base.keys := by
    subst e3
    rfl
  have g3 : s3.base.heard = some g := by
    subst e3
    rfl
  obtain ⟨cls, t, F', g', rows, keys, c1, -, hg', -, hk, e4⟩ := layerD_law d3
  have k4 : s4.base.keys = s3.base.keys ++ [keys] := by
    subst e4
    show t.base.keys ++ [keys] = _
    rw [AtPublicFiles.AtFiles.claims_keys c1]
  obtain rfl : g = g' := by
    rw [claims_heard c1, g3] at hg'
    exact Option.some.inj hg'
  have k5 : s5.base.keys = s4.base.keys := by rw [after_ok one set i x s4 s5 d4]
  have k6 : s6.base.keys = s5.base.keys := by
    rw [clear_ok one set i x s5 s6 d5]
    rfl
  refine ⟨keys, ⟨F', _, g, es, F, G, hk, hh⟩, ?_, ?_⟩
  · rw [← e7]
    show s6.base.keys = _
    rw [k6, k5, k4, k3, k2, k1]
  · rw [← e7]
    rfl

/-- At two lookups: what stands in front of the ranges' test. -/
theorem pre_two (one : Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Params.Setting) (N : H2U.PlaceNums) {x0 x1 : Lookup} (hlk : lookupsOf one = [x0, x1]) :
    keyFirstPre one D told set N =
      [(firstChain one D told set N).first.asBare,
        (sendOwnMessage (Cl := Key.Claim) one pieces
          (groupsTold told (rootsBefore D 2) (rootsAt D 2))).asBare] ++
      ((lookupLink one set 0 x0).blocksInOrder ++ ((lookupLink one set 1 x1).blocksInOrder ++ [])) ++
      [(layRows one).asBare] := by
  unfold keyFirstPre
  have e : (firstChain one D told set N).links =
      ((lookupsOf one).zipIdx 0).map fun x => lookupLink one set x.2 x.1 := rfl
  rw [e, hlk]
  rfl

/-- **OVER ALL THAT STANDS IN FRONT OF "batt.1.batt"**, at two lookups. -/
theorem front_heard (one : Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Params.Setting) (N : H2U.PlaceNums) (ft : ℕ) {x0 x1 : Lookup}
    (hlk : lookupsOf one = [x0, x1]) {s : FirstState} {seen : List Fmt.RoundView} {cols : List OpenedColumn}
    {r : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (keyFirstPre one D told set N ++ [rngEntry one N]) s seen cols = .ok r)
    (hp : stPlainB s.d.st = true) (hk0 : s.base.keys = []) :
    ∃ k0 k1, r.1.base.keys = [k0, k1] ∧ HeardOn set 0 x0 (seen.drop 4) k0 ∧
      HeardOn set 1 x1 (seen.drop (4 + lenOf set 0 x0)) k1 := by
  rw [pre_two one D told set N hlk] at h
  obtain ⟨s15, rs1, c1, f1, f2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
  obtain ⟨s14, rs2, c2, g1, g2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 f1
  obtain ⟨s2, rs3, c3, k1, k2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 g1
  obtain ⟨a1, _, _, d0, k1⟩ := fold_cons_r k1
  obtain ⟨a2, _, _, d1, k1⟩ := fold_cons_r k1
  have e2 := Except.ok.inj k1
  obtain ⟨p1, b1⟩ := idx_plain (one := one) (N := pieces) d0 hp
  obtain ⟨-, b2⟩ := msg_plain (one := one) (N := pieces) d1 p1
  have es2 : a2 = s2 := congrArg Prod.fst e2
  have er3 : (seen.drop 2).drop 2 = rs3 := congrArg (fun z => z.2.1) e2
  have er3' : rs3 = seen.drop 4 := by rw [← er3, List.drop_drop]
  obtain ⟨t1, rs4, c4, l0, l1⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 k2
  obtain ⟨t2, rs5, c5, l1, l2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 l1
  have e5 : t2 = s14 := congrArg Prod.fst (Except.ok.inj l2)
  obtain ⟨k0, H0, q0, w0⟩ := link_heard one set 0 x0 ft l0
  obtain ⟨k1', H1, q1, -⟩ := link_heard one set 1 x1 ft l1
  have w0' : rs4 = seen.drop (4 + lenOf set 0 x0) := by
    have : rs4 = rs3.drop (lenOf set 0 x0) := w0
    rw [this, er3', List.drop_drop]
  obtain ⟨a15, _, _, d14, g2⟩ := fold_cons_r g2
  have e15 : a15 = s15 := congrArg Prod.fst (Except.ok.inj g2)
  obtain ⟨-, d, -, q15⟩ := layRows_says (one := one) d14
  obtain ⟨a16, _, _, d15, f2⟩ := fold_cons_r f2
  have e16 : a16 = r.1 := congrArg Prod.fst (Except.ok.inj f2)
  obtain ⟨tE, -, q16⟩ := ranges_inv one N _ _ _ _ d15
  refine ⟨k0, k1', ?_, by rw [← er3']; exact H0, by rw [← w0']; exact H1⟩
  have z16 : a16.base.keys = s15.base.keys := by
    subst q16
    rfl
  have z15 : a15.base.keys = s14.base.keys := by
    subst q15
    rfl
  have q0' : t1.base.keys = s2.base.keys ++ [k0] := q0
  have q1' : t2.base.keys = t1.base.keys ++ [k1'] := q1
  rw [← e16, z16, ← e15, z15, ← e5, q1', q0', ← es2, b2, b1, hk0]
  rfl

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.fold_cons_r
#print axioms AtPublicFiles.FirstH.Lots.claims_heard
#print axioms AtPublicFiles.FirstH.Lots.link_heard
#print axioms AtPublicFiles.FirstH.Lots.pre_two
#print axioms AtPublicFiles.FirstH.Lots.front_heard
