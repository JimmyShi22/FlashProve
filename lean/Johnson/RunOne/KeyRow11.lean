-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow11.lean: THE KEY FILE's ROW 1.1 (msg.1.send) AT THE TABLES' LETTERS: from the general row of a sending (sendRow_keeps_new, Johnson/Desc/Key/KeySendRow.lean) and what the block's yes lays (KeySendYes1.lean). By row 1.0's pattern (KeyRow10.lean); WHAT IS NEW: an elder pin (0) with its sample's row rides.
OBJECT: Keeps (on₁ … 1) (on₁ … 2) (L₁ … 1) (L₁ … 2) pc.err · USER: keepsAt_of_law₁ at the field r1_1 · LETTERS: F Fr G at_ one R coll; pc b; N groups; ρ.
  size3_of_yes  PROVED: behind the block's yes the statement has just three messages
  keeps_send1   PROVED FROM: hheld | hrounds | hd | hr (the piece holds the block; the block decides and declares as sendOwnMessage) · Public11 (public) · hbase (the elder pin's tree lies below the piece's base) · hat (at_ 1 = (1, 0)) · THREE CONDITIONS ON LETTERS: RecStays G · SmpOwn G at_ one · R.same = «ρ a = ρ b» · CollCell coll · hnew (behind the piece every leaf of the seat at_ 1 is shown) · good | tie (GoodIn at the piece with a promise Sl behind; Sl gives hasSmp ∧ NoColl at at_ 1)
Nothing on soundness.
-/
import Johnson.RunOne.KeySendYes1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)

variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- **Behind the yes the statement has just three messages.** -/
theorem size3_of_yes (N : Pieces) (groups : List (List Nat)) (Pb : Public11 one N groups)
    (b : Block FirstState Claim) (hd : b.decide = (sendOwnMessage one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parMsg' one N groups))
    (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hf : roundsFit (held b : Block (Xi × FirstState) Claim).rounds rs = true)
    (hy : b.decide s (rs.map noDigest) gs = .ok s') (h1 : shape₁' one 1 s = true) (hI : Means.InOrder s.d.st) : s'.d.st.oracles.size = 3 := by
  have hf0 : roundsFit (K1.rounds (parMsg' one N groups)) rs = true := hr ▸ hf
  have hlen := roundsFit_length _ _ hf0
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, b0, c0, d0, i0, -⟩ := front1 one s h1
  have hf' : roundsFit (K1.rounds (parMsg' one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf0
  exact (laid1_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 b0 c0 d0 i0 hI).size

/-- The row, where the number of lookups is given. -/
theorem keeps_send1_two {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds) (hn : n₁ one = 2)
    (N : Pieces) (groups : List (List Nat)) (Pb : Public11 one N groups)
    (hd : b.decide = (sendOwnMessage one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parMsg' one N groups))
    (hbase : (at_ 0).1 < pc.base) (hat : at_ 1 = (1, 0)) (hR : RecStays G) (hG : SmpOwn G at_ one) (hcoll : CollCell coll)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 1 a → pc.ior.red.out a τ = some a' → ShownAt F at_ 1 (strsOf Fr a'.2))
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 1) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 1).1 (at_ 1).2 a'.1 = true ∧ NoColl F G (at_ 1).1 (at_ 1).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 1) (on₁ F Fr G at_ one R coll 2) (L₁ F Fr G at_ one R 1) (L₁ F Fr G at_ one R 2) pc.err := by
  have e0 : on₁ F Fr G at_ one R coll 1 = onB F Fr G at_ (meaning₁At one R) (shape₁' one 1) (free₁ F G at_ one R coll 1) (open₁ 2 1) := by
    unfold on₁ onB
    rw [hn]
  rw [e0] at hnew good
  -- what the yes lays, off the held block
  have laid : ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), roundsFit pc.b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      shape₁' one 1 s = true → Means.InOrder s.d.st → Laid1 s s' := by
    intro s s' rs gs hf hy h1 hI
    rw [hrounds, hr] at hf
    have hlen := roundsFit_length _ _ hf
    obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
      match rs, hlen with
      | [a, c], _ => exact ⟨a, c, rfl⟩
    rw [hd] at hy
    obtain ⟨a0, b0, c0, d0, i0, -⟩ := front1 one s h1
    have hf' : roundsFit (K1.rounds (parMsg' one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf
    exact laid1_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 b0 c0 d0 i0 hI
  have key := sendRow_keeps_new F Fr G at_ (meaning₁At one R) pc (shape₁' one 1) (shape₁' one 2)
    (free₁ F G at_ one R coll 1) (free₁ F G at_ one R coll 2) (open₁ 2 1) [.pin 1, .srow 1] 1 pinned_send1
    (fun j hj => by
      rw [pinned_behind0] at hj
      obtain rfl : j = 0 := by simpa using hj
      exact hbase)
    (ShownAt F at_ 1) hnew
    (fun a rs gs a' y y' hf hdd Hy hN ho => by
      obtain ⟨e, hb⟩ := hheld a _ gs a' hdd
      refine ⟨fun _ => rfl, fun hu => ?_⟩
      obtain ⟨h1, -, h3, -⟩ := ho.resolve_left (fun hx => hx hu)
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      have H := laid s s' rs gs hf hb h1 h3.2.2.2.2.2.2.1
      refine ⟨shape_send1 one Pb.stages s s' H h1, fun j hj => ?_, free_send1 F G at_ one R coll hR hcoll hat p' s s' y y' H Hy hN h3⟩
      rw [pinned_behind0] at hj
      obtain rfl : j = 0 := by simpa using hj
      exact smp_send1 G at_ one hG p' s s' H h1)
    (fun a rs gs a' y y' w hf hdd Hy ho hw => by
      obtain ⟨e, hb⟩ := hheld a _ gs a' hdd
      obtain ⟨h1, -, h3, -⟩ := ho.resolve_left (fun hx => hx rfl)
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      have H := laid s s' rs gs hf hb h1 h3.2.2.2.2.2.2.1
      exact back_send1 F G at_ one R ρ hs hR p' s s' y y' w H (front1 one s h1).1 h3.2.2.2.2.2.2.1 (smp_send1 G at_ one hG p' s s' H h1) Hy hw)
    Sl Ra Rb good tie
  unfold on₁ L₁ R₁
  rw [hn, open₁_send1]
  exact key

/-- **ROW 1.1.** The number of lookups is no premise: the promise in front holds it (on₁_two). -/
theorem keeps_send1 {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds)
    (N : Pieces) (groups : List (List Nat)) (Pb : Public11 one N groups)
    (hd : b.decide = (sendOwnMessage one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parMsg' one N groups))
    (hbase : (at_ 0).1 < pc.base) (hat : at_ 1 = (1, 0)) (hR : RecStays G) (hG : SmpOwn G at_ one) (hcoll : CollCell coll)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 1 a → pc.ior.red.out a τ = some a' → ShownAt F at_ 1 (strsOf Fr a'.2))
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 1) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 1).1 (at_ 1).2 a'.1 = true ∧ NoColl F G (at_ 1).1 (at_ 1).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 1) (on₁ F Fr G at_ one R coll 2) (L₁ F Fr G at_ one R 1) (L₁ F Fr G at_ one R 2) pc.err := by
  intro a ha
  exact keeps_send1_two F Fr G at_ one R coll ρ hs pc b hheld hrounds (on₁_two F Fr G at_ one R coll 1 a ha) N groups Pb hd hr hbase hat hR hG hcoll hnew Sl Ra Rb good tie a ha

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.size3_of_yes
#print axioms Johnson.RunOne.KeyRows1.keeps_send1
