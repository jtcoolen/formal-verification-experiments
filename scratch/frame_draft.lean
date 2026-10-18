/-! ### Clause group 3: frame conditions -/

/-- **Clause group 3 (frame conditions).**  Knowledge never shrinks, and a session that does
not act keeps its program counter and its whole store: both are instances of the frame lemmas
of ProtSat.Operational, which the characteristic assignment reads directly. -/
theorem sat_frame (hok : RunOK sh P cfg ev)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (frameClauses sh) := by
  intro cl hcl
  simp only [frameClauses, cnfOf, eachStep, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, hcl'⟩ := hcl
  rw [List.mem_append] at hcl'
  rcases hcl' with hkn | hsess
  · -- knowledge monotonicity
    simp only [frameKnClauses, mapMsg, List.mem_range] at hkn
    rw [List.mem_map] at hkn
    obtain ⟨u, hu, heq⟩ := hkn
    subst heq
    have hu' : u < shVal sh := by
      have hs : shVal sh = sh.U.length + 1 := rfl
      rw [hs]
      exact Nat.lt_succ_of_lt (by simpa using hu)
    have hc1 : assignOf sh P cfg ev (vkn sh i u) = knHolds sh cfg i u :=
      assignOf_kn sh P cfg ev (Nat.le_of_lt hi) hu'
    have hc2 : assignOf sh P cfg ev (vkn sh (i + 1) u) = knHolds sh cfg (i + 1) u :=
      assignOf_kn sh P cfg ev (Nat.succ_le_of_lt hi) hu'
    by_cases h1 : assignOf sh P cfg ev (vkn sh i u) = true
    · have hk : knHolds sh cfg i u = true := by rw [← hc1]; exact h1
      have hk2 : knHolds sh cfg (i + 1) u = true := by
        cases h : valAt sh u with
        | none => simp [knHolds, h] at hk
        | some t =>
            have hmem : t ∈ (cfg (i + 1)).kn :=
              Rel.kn_mono (hrel i) t (by simpa [knHolds, h] using hk)
            simpa [knHolds, h] using hmem
      exact clause2_right _ _ _ (by rw [pos_eval, hc2]; exact hk2)
    · exact clause2_left _ _ _ (by simp [neg_eval, h1])
  · simp only [eachSess, List.mem_flatMap, List.mem_range] at hsess
    obtain ⟨q, hq, hcl''⟩ := hsess
    rw [frameSessClauses, List.mem_append] at hcl''
    rcases hcl'' with hpc | hst
    · rw [List.mem_map] at hpc
      obtain ⟨c, hc, heq⟩ := hpc
      subst heq
      rcases bool_eq_cases (assignOf sh P cfg ev (evAct sh i q)) with hact | hact
      · exact clause3_left _ _ _ _ (by simp [pos_eval, hact])
      · refine clause3_right _ _ _ _ ?_
        have hne : ¬ ∃ m d, ev i = Ev.act q m d := by
          intro ex
          obtain ⟨m, d, hex⟩ := ex
          have h4 : rdEv sh P cfg ev i = 1 + q := rdEv_act sh P cfg ev hex
          have h5 : assignOf sh P cfg ev (evAct sh i q)
              = decide (rdEv sh P cfg ev i = 1 + q) := assignOf_evAct sh P cfg ev hi hq
          rw [h5, h4] at hact
          exact by simpa using hact
        obtain ⟨hpc', _, _⟩ := Rel.noAct (hrel i) q hne
        rcases bool_eq_cases (assignOf sh P cfg ev (vpc sh i q c)) with h2 | h2
        · have h9 : pcOf (cfg (i + 1)) q = c := by
            rw [hpc']
            have h2'' : decide (rdPc sh P cfg ev i q = c) = true := by
              rw [← assignOf_pc sh P cfg ev (Nat.le_of_lt hi) hq (by simpa using hc)]
              exact h2
            exact of_decide_eq_true h2''
          refine clause3_right (assignOf sh P cfg ev) (pos (evAct sh i q)) (neg (vpc sh i q c))
            (pos (vpc sh (i + 1) q c)) ?_
          rw [pos_eval, assignOf_pc sh P cfg ev (Nat.succ_le_of_lt hi) hq (by simpa using hc)]
          show decide (pcOf (cfg (i + 1)) q = c) = true
          rw [h9]
          exact decide_eq_true rfl
        · refine clause3_mid (assignOf sh P cfg ev) (pos (evAct sh i q)) (neg (vpc sh i q c))
            (pos (vpc sh (i + 1) q c)) ?_
          rw [neg_eval]
          rw [h2]
    · obtain ⟨x, hx, h3⟩ := List.mem_flatMap.mp hst
      simp only [mapVal, List.mem_range] at h3
      rw [List.mem_map] at h3
      obtain ⟨u, hu, heq⟩ := h3
      subst heq
      rcases bool_eq_cases (assignOf sh P cfg ev (evAct sh i q)) with hact | hact
      · exact clause3_left _ _ _ _ (by simp [pos_eval, hact])
      · refine clause3_right _ _ _ _ ?_
        have hne : ¬ ∃ m d, ev i = Ev.act q m d := by
          intro ex
          obtain ⟨m, d, hex⟩ := ex
          have h4 : rdEv sh P cfg ev i = 1 + q := rdEv_act sh P cfg ev hex
          have h5 : assignOf sh P cfg ev (evAct sh i q)
              = decide (rdEv sh P cfg ev i = 1 + q) := assignOf_evAct sh P cfg ev hi hq
          rw [h5, h4] at hact
          exact by simpa using hact
        obtain ⟨_, hst', _⟩ := Rel.noAct (hrel i) q hne
        rcases bool_eq_cases (assignOf sh P cfg ev (vst sh i q x u)) with h2 | h2
        · have h9 : uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = u := by
            rw [hst']
            have h2'' : decide (rdSt sh P cfg ev i q x = u) = true := by
              rw [← assignOf_st sh P cfg ev (Nat.le_of_lt hi) hq (by simpa using hx)
                (by simpa using hu)]
              exact h2
            exact of_decide_eq_true h2''
          refine clause3_right (assignOf sh P cfg ev) (pos (evAct sh i q)) (neg (vst sh i q x u))
            (pos (vst sh (i + 1) q x u)) ?_
          rw [pos_eval, assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq (by simpa using hx)
            (by simpa using hu)]
          show decide (uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = u) = true
          rw [h9]
          exact decide_eq_true rfl
        · refine clause3_mid (assignOf sh P cfg ev) (pos (evAct sh i q)) (neg (vst sh i q x u))
            (pos (vst sh (i + 1) q x u)) ?_
          rw [neg_eval]
          rw [h2]


