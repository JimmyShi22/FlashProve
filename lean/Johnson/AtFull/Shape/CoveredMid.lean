-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/CoveredMid.lean: THE HEAD's READS (member 342 of the proof file's own first
chain): ITS TEST ON VALUES ASKS "THE COVERED POSITIONS CAN BE MADE" AT THE STATE BEHIND THE MEMBER's
OWN COMMITMENT, not at a border: HERE THAT CLAUSE IS CARRIED BACK TO THE BORDER, WHERE
ReqReplyReach.lean pays it. Under the head P5J.AtMgA. A joining of laws; nothing is evaluated.

  `commit_req`: GENERAL: a yes of a segment's later commitment at the record (K1.commitAtS,
    Johnson/Desc/K1/AtS.lean) leaves the request's words. (That it leaves what the chain puts out is
    the library's: K1.commitAtS_ok, Johnson/Desc/K1/Law/AtRecord.lean.)
  `covered_mid`: GENERAL: so the covered positions are behind it what they were in front.
  **`midV_covered_of`**: GENERAL: the commitment returns at what midV (ReadsFrames.lean) hands it,
    and the covered positions can be made in front: then midV accepts at that test.
  **`tab_342_vals`**: the table's own test at 342 is midV at that test, at the ground's numbers.
  **`vals_342_reach`**: under the head, with Bs what ProofFile.baseOf returns at the public part: at every
    state reached at border 342 (Reach, Johnson/Top/H0/Walk/Reach.lean: the raw family), at an
    instance whose request passes the start's test: where the commitment returns, the table's test
    at 342 accepts.

Limits. THAT THE COMMITMENT RETURNS IS A HYPOTHESIS: it is the member's own first half: the step on
shapes and the fit of the rounds are meant to give it: not called here. That anything is reached is
not said. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.

-/
import Johnson.AtFull.Shape.TableFramesV
import Johnson.AtFull.Shape.ReqReplyReach
import Johnson.Desc.K1.Law.InOrderAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain K1.commitAtS)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- A yes of a later commitment at the record leaves the request's words. -/
theorem commit_req {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (K1.commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.req = s.req := by
  unfold K1.commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, _, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 h
    rw [VerifiableInference.Desc.K1.putFork_req, VerifiableInference.Desc.K1.putLink_req]
    rfl
  · cases h

/-- So the covered positions are behind it what they were in front. -/
theorem covered_mid {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (K1.commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') (T V : Nat) :
    s'.covered T V = s.covered T V := by
  obtain ⟨_, _, -, -, -, ho⟩ := VerifiableInference.Desc.K1.commitAtS_ok P link moment arrays s s'
    rs gs h
  exact covered_congr (commit_req P link moment arrays s s' rs gs h) (by rw [ho]) T V

/-- **Where the commitment returns and the covered positions can be made in front, the test at the
state behind the commitment accepts.** -/
theorem midV_covered_of {P : VerifiableInference.Desc.K1.Par} {link : Nat}
    {arrays : Option (List Nat)} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {T V : Nat}
    (hc : ∃ m, (K1.commitAtS (Cl := Unit) P link 1 arrays).decide s rs
      (gs.take (K1.commitAtS (Cl := Unit) P link 1 arrays).openings) = .ok m)
    (hv : ∃ cov, s.covered T V = .ok cov) :
    midV P link arrays (fun m => (m.covered T V).toOption.isSome) s rs gs = true := by
  obtain ⟨m, hm⟩ := hc
  obtain ⟨cov, hcov⟩ := hv
  unfold midV
  rw [hm]
  show (m.covered T V).toOption.isSome = true
  rw [covered_mid P link 1 arrays s m rs _ hm T V, hcov]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **The table's own test at 342.** -/
theorem tab_342_vals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∃ rd : Option (List Nat), (Tab.nums Bs.G₀ 24).map (·.2.2.1) = some rd ∧
      ∀ s rs gs, Tab.vals Zp Bs.G₀ 342 s rs gs =
        midV (Tab.k1P Zp Bs.G₀ 24 5 1) 24 rd
          (fun m => (m.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome) s rs gs := by
  obtain ⟨B', Xl, pd, reads, digits, -, e1, e2, e3, -⟩ := reads_head_frame_free h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 342 = Tab.readsHead Zp Bs.G₀ :=
    cells_head Zp Bs.G₀ 5 (by omega) rfl
  unfold Tab.readsHead at hc
  rw [nums_of e2 e3] at hc
  exact ⟨_, by rw [nums_of e2 e3]; rfl, fun s rs gs => by rw [cell_v hc]⟩

/-- **At every state reached at border 342: where the commitment returns, the table's test
accepts.** -/
theorem vals_342_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∃ rd : Option (List Nat), (Tab.nums Bs.G₀ 24).map (·.2.2.1) = some rd ∧
      ∀ {a : ProofFile.InstPub × S}, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 342 a →
      (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true →
      ∀ rs gs, (∃ m, (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 rd).decide a.2 rs
        (gs.take (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 rd).openings) = .ok m) →
      Tab.vals Zp Bs.G₀ 342 a.2 rs gs = true := by
  obtain ⟨rd, erd, hv⟩ := tab_342_vals h hB
  obtain ⟨Bs', hB', hc⟩ := covered_reach_ground h
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  refine ⟨rd, erd, fun hr hq rs gs hm => ?_⟩
  rw [hv]
  exact midV_covered_of hm (hc hr hq (by omega))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.commit_req
#print axioms Johnson.AtFull.Shape.covered_mid
#print axioms Johnson.AtFull.Shape.midV_covered_of
#print axioms Johnson.AtFull.Shape.tab_342_vals
#print axioms Johnson.AtFull.Shape.vals_342_reach
