-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow117.lean: THE KEY FILE's ROW 1.17 (w.1.send) AT THE TABLES' LETTERS: from the general row of a sending (sendRow_keeps_new, Johnson/Desc/Key/KeySendRow.lean) and what the block's yes lays (KeyWLaid | KeyWShape). BY ROW 1.1's PATTERN, TO THE STEP (KeyRow11.lean: size3_of_yes · keeps_send1_two · keeps_send1).
OBJECT: Keeps (on₁ … 17) (on₁ … 18) (L₁ … 17) (L₁ … 18) pc.err · USER: keepsAt_of_law₁ at the field r1_17 · LETTERS: F Fr G at_ one R coll; pc b bw; N sent groups; ρ.
  sizeW_of_yes   PROVED: behind the block's yes the statement has just wAt one + 2 messages
  keeps_send17   PROVED FROM: hheld | hrounds | hd | hr (the piece holds the block; the block decides as sendW's (Johnson/Desc/Key/One.lean) and declares the sending kind's two rounds) · Public117 · «W's mask's number is below noId» (public) · hbase (the elder pin's tree lies below the piece's base) · hat (at_ 2 = (st + 1, 0)) · FOUR CONDITIONS ON LETTERS: RecStays G · SmpOwn G at_ one · R.same = «ρ a = ρ b» · CollCell coll · hnew (behind the piece every leaf of the seat at_ 2 is shown) · good | tie (GoodIn at the piece with a promise Sl behind; Sl gives hasSmp ∧ NoColl at at_ 2)
Nothing on soundness.
-/
import Johnson.RunOne.KeyWShape
import Johnson.RunOne.KeyRow11

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

theorem pinned_send17 : pinned (open₁ 2 17 ++ [.pin 2, .srow 2]) = pinned (open₁ 2 17) ++ [2] := by decide +kernel

/-- What the yes lays, off a block that decides as the seat's. -/
theorem laid17_at (N : Pieces) (sent : Nat) (groups : List (List Nat)) (Pb : Public117 one N groups) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (b : Block FirstState Claim) (hd : b.decide = bw.decide) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hf : roundsFit (K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂])) rs = true)
    (hy : b.decide s (rs.map noDigest) gs = .ok s') (h1 : shape₁' one 17 s = true) (hI : Means.InOrder s.d.st) : Laid17 one s s' := by
  have hlen := roundsFit_length _ _ hf
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, b0, c0, d0, m0⟩ := front17 one s h1
  have hf' : roundsFit (K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂])) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf
  exact laid17_of one N sent groups Pb bw hb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 b0 c0 d0 m0 hI

/-- **Behind the yes the statement has just wAt one + 2 messages.** -/
theorem sizeW_of_yes (N : Pieces) (sent : Nat) (groups : List (List Nat)) (Pb : Public117 one N groups) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (b : Block FirstState Claim) (hd : b.decide = bw.decide) (hr : b.rounds = K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂]))
    (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hf : roundsFit (held b : Block (Xi × FirstState) Claim).rounds rs = true)
    (hy : b.decide s (rs.map noDigest) gs = .ok s') (h1 : shape₁' one 17 s = true) (hI : Means.InOrder s.d.st) : s'.d.st.oracles.size = wAt one + 2 :=
  (laid17_at one N sent groups Pb bw hb b hd s s' rs gs (hr ▸ hf) hy h1 hI).size

/-- The row, where the number of lookups is given. -/
theorem keeps_send17_two {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds) (hn : n₁ one = 2)
    (N : Pieces) (sent : Nat) (groups : List (List Nat)) (Pb : Public117 one N groups) (hsm : wAt one + 1 < noId) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (hd : b.decide = bw.decide) (hr : b.rounds = K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂]))
    (hbase : (at_ 0).1 < pc.base) (hat : at_ 2 = (one.ranges.stages.length + 1, 0)) (hR : RecStays G) (hG : SmpOwn G at_ one) (hcoll : CollCell coll)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 17 a → pc.ior.red.out a τ = some a' → ShownAt F at_ 2 (strsOf Fr a'.2))
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 17) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 2).1 (at_ 2).2 a'.1 = true ∧ NoColl F G (at_ 2).1 (at_ 2).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 17) (on₁ F Fr G at_ one R coll 18) (L₁ F Fr G at_ one R 17) (L₁ F Fr G at_ one R 18) pc.err := by
  have e0 : on₁ F Fr G at_ one R coll 17 = onB F Fr G at_ (meaning₁At one R) (shape₁' one 17) (free₁ F G at_ one R coll 17) (open₁ 2 17) := by
    unfold on₁ onB
    rw [hn]
  rw [e0] at hnew good
  have laid : ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), roundsFit pc.b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      shape₁' one 17 s = true → Means.InOrder s.d.st → Laid17 one s s' := by
    intro s s' rs gs hf hy h1 hI
    rw [hrounds, hr] at hf
    exact laid17_at one N sent groups Pb bw hb b hd s s' rs gs hf hy h1 hI
  have key := sendRow_keeps_new F Fr G at_ (meaning₁At one R) pc (shape₁' one 17) (shape₁' one 18)
    (free₁ F G at_ one R coll 17) (free₁ F G at_ one R coll 18) (open₁ 2 17) [.pin 2, .srow 2] 2 pinned_send17
    (fun j hj => by
      rw [pinned_at17] at hj
      obtain rfl : j = 0 := by simpa using hj
      exact hbase)
    (ShownAt F at_ 2) hnew
    (fun a rs gs a' y y' hf hdd Hy hN ho => by
      obtain ⟨e, hb'⟩ := hheld a _ gs a' hdd
      refine ⟨fun _ => rfl, fun hu => ?_⟩
      obtain ⟨h1, -, h3, -⟩ := ho.resolve_left (fun hx => hx hu)
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      have H := laid s s' rs gs hf hb' h1 h3.2.2.2.2.2.2.1
      refine ⟨shape_send17 one hsm s s' H h1, fun j hj => ?_, free_send17 F G at_ one R coll hR hcoll hat p' s s' y y' H Hy hN h3⟩
      rw [pinned_at17] at hj
      obtain rfl : j = 0 := by simpa using hj
      exact smp_send17 G at_ one hG p' s s' H (front17 one s h1).1)
    (fun a rs gs a' y y' w hf hdd Hy ho hw => by
      obtain ⟨e, hb'⟩ := hheld a _ gs a' hdd
      obtain ⟨h1, -, h3, -⟩ := ho.resolve_left (fun hx => hx rfl)
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      have H := laid s s' rs gs hf hb' h1 h3.2.2.2.2.2.2.1
      exact back_send17 F G at_ one R ρ hs hR p' s s' y y' w H (front17 one s h1).1 h3.2.2.2.2.2.2.1 (smp_send17 G at_ one hG p' s s' H (front17 one s h1).1) Hy hw)
    Sl Ra Rb good tie
  unfold on₁ L₁ R₁
  rw [hn, open₁_send17]
  exact key

/-- **ROW 1.17.** The number of lookups is no premise: the promise in front holds it (on₁_two). -/
theorem keeps_send17 {K : Type} [CommRing K] (ρ : Model.Reading K) (hs : R.same = fun a b => ρ.val a = ρ.val b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds)
    (N : Pieces) (sent : Nat) (groups : List (List Nat)) (Pb : Public117 one N groups) (hsm : wAt one + 1 < noId) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (hd : b.decide = bw.decide) (hr : b.rounds = K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂]))
    (hbase : (at_ 0).1 < pc.base) (hat : at_ 2 = (one.ranges.stages.length + 1, 0)) (hR : RecStays G) (hG : SmpOwn G at_ one) (hcoll : CollCell coll)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 17 a → pc.ior.red.out a τ = some a' → ShownAt F at_ 2 (strsOf Fr a'.2))
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 17) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 2).1 (at_ 2).2 a'.1 = true ∧ NoColl F G (at_ 2).1 (at_ 2).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 17) (on₁ F Fr G at_ one R coll 18) (L₁ F Fr G at_ one R 17) (L₁ F Fr G at_ one R 18) pc.err := by
  intro a ha
  exact keeps_send17_two F Fr G at_ one R coll ρ hs pc b hheld hrounds (on₁_two F Fr G at_ one R coll 17 a ha) N sent groups Pb hsm bw hb hd hr hbase hat hR hG hcoll hnew Sl Ra Rb good tie a ha

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.sizeW_of_yes
#print axioms Johnson.RunOne.KeyRows1.keeps_send17
