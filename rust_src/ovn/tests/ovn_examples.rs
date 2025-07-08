use hacspec_concordium::*;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

pub use hacspec_ovn::ovn_group::*;
pub use hacspec_ovn::ovn_secp256k1::*;
pub use hacspec_ovn::ovn_z89::*;
pub use hacspec_ovn::ovn_z18446744073709551557::*;
use rand::random;

#[cfg(test)]
pub fn schnorr_zkp_correctness<G: Group>(random_x: u128, random_r: u128) -> bool {
    let x: G::Z = G::Z::random_field_elem(random_x);
    let r: G::Z = G::Z::random_field_elem(random_r);

    let pow_x = G::g_pow(x);

    let pi: SchnorrZKPCommit<G> = schnorr_zkp(r, pow_x, x);

    let valid = schnorr_zkp_validate::<G>(pow_x, pi);
    valid
}

#[test]
pub fn schnorr_zkp_z_89_correctness() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(schnorr_zkp_correctness::<g_z_89> as fn(u128, u128) -> bool)
}

#[test]
pub fn schnorr_zkp_z_18446744073709551557_correctness() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(schnorr_zkp_correctness::<g_z_18446744073709551557> as fn(u128, u128) -> bool)
}

#[test]
pub fn schorr_zkp_secp256k1_correctness() {
    QuickCheck::new()
        .tests(10)
        .quickcheck(schnorr_zkp_correctness::<Group_curve> as fn(u128, u128) -> bool)
}

#[cfg(test)]
pub fn or_zkp_correctness<G: Group>(
    random_w: u128,
    random_r: u128,
    random_d: u128,
    random_h: u128,
    random_x: u128,
    v: bool,
) -> bool {
    let w = G::Z::random_field_elem(random_w);
    let r = G::Z::random_field_elem(random_r);
    let d = G::Z::random_field_elem(random_d);
    let h = G::Z::random_field_elem(random_h);
    let x = G::Z::random_field_elem(random_x);

    let mut h = G::g_pow(h);
    let x = x;
    let pi: OrZKPCommit<G> = zkp_one_out_of_two(w, r, d, h, x, v);
    let valid = zkp_one_out_of_two_validate::<G>(h, pi);
    valid
}

#[test]
pub fn or_zkp_correctness_z89() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(or_zkp_correctness::<g_z_89> as fn(u128, u128, u128, u128, u128, bool) -> bool)
}

#[test]
pub fn or_zkp_correctness_z18446744073709551557() {
    QuickCheck::new()
        .tests(10000)
        .quickcheck(or_zkp_correctness::<g_z_18446744073709551557> as fn(u128, u128, u128, u128, u128, bool) -> bool)
}

#[test]
// TODO: Fix inverse opeation, should make this test parse
pub fn or_zkp_secp256k1_correctness() {
    QuickCheck::new().tests(10).quickcheck(
        or_zkp_correctness::<Group_curve> as fn(u128, u128, u128, u128, u128, bool) -> bool,
    )
}

#[cfg(test)]
pub fn sum_to_zero<G: Group, const n: usize>() {
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut g_pow_xis: [G; n] = [G::group_one(); n];
    use rand::random;
    for i in 0..n {
        xis[i] = G::Z::random_field_elem(random());
        g_pow_xis[i] = G::g_pow(xis[i]);
    }

    let mut res = G::group_one();
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i, g_pow_xis);
        res = G::prod(res , /* group product */  G::pow(g_pow_yi, xis[i]));
    }

    assert!(res == G::group_one());
}

#[test]
pub fn sum_to_zero_z89() {
    sum_to_zero::<g_z_89, 55>()
}

#[test]
pub fn sum_to_zero_z18446744073709551557() {
    sum_to_zero::<g_z_18446744073709551557, 555>()
}

#[test]
pub fn sum_to_zero_secp256k1() {
    sum_to_zero::<Group_curve, 55>()
}

#[derive(Copy, Clone, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct ElemOfEach<G : Group> {
    i : u32,
    z : G::Z,
    g : G,
}

#[cfg(test)]
pub fn test_params_of_group<
    G: Group,
    A: HasActions,
    >() {
    // Setup the context
    let mut ctx = hacspec_concordium::test_infrastructure::ReceiveContextTest::empty();
    let parameter = ElemOfEach::<G> {
        i: random(),
        z: G::Z::random_field_elem(random()),
        g: G::g_pow(G::Z::random_field_elem(random())),
    };
    let parameter_bytes = to_bytes(&parameter);
    let ctx_params = ctx.set_parameter(&parameter_bytes);
    let param_back: Result<ElemOfEach<G>, ParseError> =
        ctx_params.parameter_cursor().get();
    assert!(param_back.is_ok());

    let wu_param = param_back.unwrap();
    assert!(wu_param.i == parameter.i);
    assert!(wu_param.z == parameter.z);
    assert!(wu_param.g == parameter.g);
}

#[test]
pub fn test_params_of_group_z89() {
    test_params_of_group::<g_z_89, hacspec_concordium::test_infrastructure::ActionsTree>()
}

#[test]
pub fn test_params_of_group_secp256k1() {
    test_params_of_group::<Group_curve, hacspec_concordium::test_infrastructure::ActionsTree>()
}

#[cfg(test)]
pub fn test_correctness<G: Group, const n: usize, A: HasActions>(
    votes: [bool; n],
    xis: [G::Z; n],
    rp_zkp_randoms: [G::Z; n],
    cvp_zkp_random_ws1: [G::Z; n],
    cvp_zkp_random_rs1: [G::Z; n],
    cvp_zkp_random_ds1: [G::Z; n],
    cvp_zkp_random_ws2: [G::Z; n],
    cvp_zkp_random_rs2: [G::Z; n],
    cvp_zkp_random_ds2: [G::Z; n],
) -> bool {
    // Setup the context
    let mut ctx : test_infrastructure::ContextTest<_> = test_infrastructure::ReceiveContextTest::empty();

    let init_ctx : test_infrastructure::ContextTest<_> = test_infrastructure::InitContextTest::empty();
    let mut state: OvnContractState<G, n> = init_ovn_contract(&init_ctx).unwrap();

    for i in 0..n {
        let parameter = RegisterParam::<G::Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            register_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    for i in 0..n {
                let private_param = CommitVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let commit_vi = commit_to_vote_private(private_param, state);

        let parameter = CommitVoteParamPublic::<G::Z> {
            cvp_i: i as u32,
            cvp_commit_vi: commit_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            commit_to_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    for i in 0..n {
        let private_param = CastVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let (zkp_vi, g_pow_yi_xi_vi) = cast_vote_private(private_param, state);

        let parameter = CastVoteParamPublic::<G> {
            cvp_i: i as u32,
            cvp_zkp_vi: zkp_vi,
            cvp_g_pow_xi_yi_vi: g_pow_yi_xi_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            cast_vote::<G, n, A>(&ctx, state).unwrap();
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<G, n, A>(&ctx, state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1;
        }
    }

    assert_eq!(state.tally, count);
    state.tally == count
}

#[cfg(test)]
fn randomized_full_test<G: Group, const n: usize>() -> bool {
    use rand::random;
    let mut votes: [bool; n] = [false; n];
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut rp_zkp_randoms: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ws1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds1: [G::Z; n] = [G::Z::field_zero(); n];

    let mut cvp_zkp_random_ws2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds2: [G::Z; n] = [G::Z::field_zero(); n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = G::Z::random_field_elem(random());
        rp_zkp_randoms[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds2[i] = G::Z::random_field_elem(random());
    }

    test_correctness::<G, n, hacspec_concordium::test_infrastructure::ActionsTree>(
        votes,
        xis,
        rp_zkp_randoms,
        cvp_zkp_random_ws1,
        cvp_zkp_random_rs1,
        cvp_zkp_random_ds1,
        cvp_zkp_random_ws2,
        cvp_zkp_random_rs2,
        cvp_zkp_random_ds2,
    )
}

// #[concordium_test]
#[test]
fn test_full_z89() {
    QuickCheck::new()
        .tests(100)
        .quickcheck(randomized_full_test::<g_z_89, 55> as fn() -> bool)
}

// #[concordium_test]
#[test]
fn test_full_z18446744073709551557() {
    QuickCheck::new()
        .tests(5)
        .quickcheck(randomized_full_test::<g_z_18446744073709551557, 555> as fn() -> bool)
}

// #[concordium_test]
#[test]
fn test_full_secp256k1() {
    QuickCheck::new()
        .tests(1)
        .quickcheck(randomized_full_test::<Group_curve, 15> as fn() -> bool)
}

#[cfg(test)]
pub fn test_attack_g_pow_yi_zero<G: Group, const n: usize, A: HasActions>(
    votes: [bool; n],
    mut xis: [G::Z; n],
    rp_zkp_randoms: [G::Z; n],
    cvp_zkp_random_ws1: [G::Z; n],
    cvp_zkp_random_rs1: [G::Z; n],
    cvp_zkp_random_ds1: [G::Z; n],
    cvp_zkp_random_ws2: [G::Z; n],
    cvp_zkp_random_rs2: [G::Z; n],
    cvp_zkp_random_ds2: [G::Z; n],
    target : usize,
    order: u128,
) -> bool {
    // Setup the context
    let mut ctx : test_infrastructure::ContextTest<_> = test_infrastructure::ReceiveContextTest::empty();
    let mut did_leak = false;

    let init_ctx : test_infrastructure::ContextTest<_> = test_infrastructure::InitContextTest::empty();
    let mut state: OvnContractState<G, n> = init_ovn_contract(&init_ctx).unwrap();

    for i in 0..n-1 {
        let parameter = RegisterParam::<G::Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            register_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    // Inject malicious secret key
    {
        let mut prod1 = G::group_one();
        for j in 0..target {
            prod1 = G::prod(prod1, state.g_pow_xis[j]);
        }

        let mut prod2 = G::group_one();
        for j in (target + 1)..n-1 {
            prod2 = G::prod(prod2, state.g_pow_xis[j]);
        }

        for xj in 0..order {
            if xj > 1000000 {
                // unrealistic attack?
                return true;
            }

            if prod1 == G::prod(prod2, G::g_pow(G::Z::random_field_elem(xj))) {
                xis[n-1] = G::Z::random_field_elem(xj);
                break;
            }
        }

        let parameter = RegisterParam::<G::Z> {
            rp_i: (n-1) as u32,
            rp_xi: xis[n-1],
            rp_zkp_random: rp_zkp_randoms[n-1],
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            register_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    for i in 0..n {
        let private_param = CommitVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let commit_vi = commit_to_vote_private(private_param, state);

        let parameter = CommitVoteParamPublic::<G::Z> {
            cvp_i: i as u32,
            cvp_commit_vi: commit_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            commit_to_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    for i in 0..n {
                let private_param = CastVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let (zkp_vi, g_pow_yi_xi_vi) = cast_vote_private(private_param, state);

        let parameter = CastVoteParamPublic::<G> {
            cvp_i: i as u32,
            cvp_zkp_vi: zkp_vi,
            cvp_g_pow_xi_yi_vi: g_pow_yi_xi_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            cast_vote::<G, n, A>(&ctx, state).unwrap();
    }

    println!("target: {}", target);
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i, state.g_pow_xis);
        if g_pow_yi == G::group_one() {
            println!("leak");
            let vote_i = state.g_pow_xi_yi_vis[i] == G::g();
            println!("vote {} vs guess {} for {}", votes[i], vote_i, i);
            assert!(vote_i == votes[i]);
            did_leak = true;
        }
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<G, n, A>(&ctx, state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1;
        }
    }

    assert_eq!(state.tally, count);
    assert!(!did_leak);
    state.tally == count
}

#[cfg(test)]
fn full_attack_test<G: Group, const n: usize, const order: u128>() -> bool {
    use rand::random;
    let mut votes: [bool; n] = [false; n];
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut rp_zkp_randoms: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ws1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds1: [G::Z; n] = [G::Z::field_zero(); n];

    let mut cvp_zkp_random_ws2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds2: [G::Z; n] = [G::Z::field_zero(); n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = G::Z::random_field_elem(random());
        rp_zkp_randoms[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds2[i] = G::Z::random_field_elem(random());
    }

    let target = random::<usize>() % n;

    test_attack_g_pow_yi_zero::<G, n, hacspec_concordium::test_infrastructure::ActionsTree>(
        votes,
        xis,
        rp_zkp_randoms,
        cvp_zkp_random_ws1,
        cvp_zkp_random_rs1,
        cvp_zkp_random_ds1,
        cvp_zkp_random_ws2,
        cvp_zkp_random_rs2,
        cvp_zkp_random_ds2,
        target,
        order
    )
}

// #[test]
// fn test_attack_g_pow_yi_zero_z89() {
//     QuickCheck::new()
//         .tests(100)
//         .quickcheck(full_attack_test::<g_z_89, 55, 89u128> as fn() -> bool)
// }

// #[test]
// fn test_attack_g_pow_yi_zero_z18446744073709551557() {
//     QuickCheck::new()
//         .tests(5)
//         .quickcheck(full_attack_test::<g_z_18446744073709551557, 555, 18446744073709551557u128> as fn() -> bool)
// }



#[cfg(test)]
pub fn test_attack_2_g_pow_yi_zero<G: Group, const n: usize, A: HasActions>(
    votes: [bool; n],
    mut xis: [G::Z; n],
    rp_zkp_randoms: [G::Z; n],
    cvp_zkp_random_ws1: [G::Z; n],
    cvp_zkp_random_rs1: [G::Z; n],
    cvp_zkp_random_ds1: [G::Z; n],
    cvp_zkp_random_ws2: [G::Z; n],
    cvp_zkp_random_rs2: [G::Z; n],
    cvp_zkp_random_ds2: [G::Z; n],
    order: u128,
) -> bool {
    // Setup the context
    let mut ctx : test_infrastructure::ContextTest<_> = test_infrastructure::ReceiveContextTest::empty();
    let mut did_leak = false;

    let init_ctx : test_infrastructure::ContextTest<_> = test_infrastructure::InitContextTest::empty();
    let mut state: OvnContractState<G, n> = init_ovn_contract(&init_ctx).unwrap();

    for i in 0..n-1 {
        let parameter = RegisterParam::<G::Z> {
            rp_i: i as u32,
            rp_xi: xis[i],
            rp_zkp_random: rp_zkp_randoms[i],
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            register_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    // Inject malicious secret key
    let mut valid_targets = Vec::new();
    let mut final_order = 0;
    for xj in 0..order {
        if xj > 1000000 {
            // unrealistic attack?
            return true;
        }

        let z_xj = G::Z::random_field_elem(xj);
        let g_pow_xj = G::g_pow(z_xj);

        for target in 0..n-1 {
            let mut prod1 = G::group_one();
            for j in 0..target {
                prod1 = G::prod(prod1, state.g_pow_xis[j]);
            }

            let mut prod2 = G::group_one();
            for j in (target + 1)..n-1 {
                prod2 = G::prod(prod2, state.g_pow_xis[j]);
            }

            if prod1 == G::prod(prod2, g_pow_xj) {
                valid_targets.push(target);
            }
        }

        if !valid_targets.is_empty() {
            xis[n-1] = z_xj;
            final_order = xj;

            let parameter = RegisterParam::<G::Z> {
                rp_i: (n-1) as u32,
                rp_xi: xis[n-1],
                rp_zkp_random: rp_zkp_randoms[n-1],
            };
            let parameter_bytes = to_bytes(&parameter);
            let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
            ctx = ctx.set_parameter(pb);
            (_, state) =
                register_vote::<G, n, A>(&ctx, state)
                .unwrap();
            break;
        }
    }

    for i in 0..n {
        let private_param = CommitVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let commit_vi = commit_to_vote_private(private_param, state);

        let parameter = CommitVoteParamPublic::<G::Z> {
            cvp_i: i as u32,
            cvp_commit_vi: commit_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            commit_to_vote::<G, n, A>(&ctx, state)
                .unwrap();
    }

    for i in 0..n {
        let private_param = CastVoteParamPrivate::<G::Z> {
            cvp_i: i as u32,
            cvp_xi: xis[i],
            cvp_zkp_random_w: cvp_zkp_random_ws2[i],
            cvp_zkp_random_r: cvp_zkp_random_rs2[i],
            cvp_zkp_random_d: cvp_zkp_random_ds2[i],
            cvp_vote: votes[i],
        };
        let (zkp_vi, g_pow_yi_xi_vi) = cast_vote_private(private_param, state);

        let parameter = CastVoteParamPublic::<G> {
            cvp_i: i as u32,
            cvp_zkp_vi: zkp_vi,
            cvp_g_pow_xi_yi_vi: g_pow_yi_xi_vi,
        };
        let parameter_bytes = to_bytes(&parameter);
        let pb : &[u8] = unsafe { std::slice::from_raw_parts(parameter_bytes.as_ptr(), parameter_bytes.len() * mem::size_of::<u8>()) };
        ctx = ctx.set_parameter(pb);
        (_, state) =
            cast_vote::<G, n, A>(&ctx, state).unwrap();
    }

    println!("target: {:?} after {}", valid_targets, final_order);
    for i in 0..n {
        let g_pow_yi = compute_g_pow_yi::<G, n>(i, state.g_pow_xis);
        if g_pow_yi == G::group_one() {
            println!("leak");
            let vote_i = state.g_pow_xi_yi_vis[i] == G::g();
            println!("vote {} vs guess {} for {}", votes[i], vote_i, i);
            assert!(vote_i == votes[i]);
            did_leak = true;
        }
    }

    let parameter = TallyParameter {};
    let parameter_bytes = to_bytes(&parameter);
    ctx = ctx.set_parameter(&parameter_bytes);

    (_, state) = tally_votes::<G, n, A>(&ctx, state).unwrap();

    let mut count = 0u32;
    for v in votes {
        if v {
            count = count + 1;
        }
    }

    assert_eq!(state.tally, count);
    assert!(!did_leak);
    state.tally == count
}

#[cfg(test)]
fn full_attack_2_test<G: Group, const n: usize, const order: u128>() -> bool {
    use rand::random;
    let mut votes: [bool; n] = [false; n];
    let mut xis: [G::Z; n] = [G::Z::field_zero(); n];
    let mut rp_zkp_randoms: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ws1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs1: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds1: [G::Z; n] = [G::Z::field_zero(); n];

    let mut cvp_zkp_random_ws2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_rs2: [G::Z; n] = [G::Z::field_zero(); n];
    let mut cvp_zkp_random_ds2: [G::Z; n] = [G::Z::field_zero(); n];

    for i in 0..n {
        votes[i] = random();
        xis[i] = G::Z::random_field_elem(random());
        rp_zkp_randoms[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds1[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ws2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_rs2[i] = G::Z::random_field_elem(random());
        cvp_zkp_random_ds2[i] = G::Z::random_field_elem(random());
    }

    test_attack_2_g_pow_yi_zero::<G, n, hacspec_concordium::test_infrastructure::ActionsTree>(
        votes,
        xis,
        rp_zkp_randoms,
        cvp_zkp_random_ws1,
        cvp_zkp_random_rs1,
        cvp_zkp_random_ds1,
        cvp_zkp_random_ws2,
        cvp_zkp_random_rs2,
        cvp_zkp_random_ds2,
        order
    )
}

// #[test]
// fn test_attack_2_g_pow_yi_zero_z89() {
//     QuickCheck::new()
//         .tests(100)
//         .quickcheck(full_attack_2_test::<g_z_89, 55, 89u128> as fn() -> bool)
// }

// #[test]
// fn test_attack_2_g_pow_yi_zero_z18446744073709551557() {
//     QuickCheck::new()
//         .tests(100)
//         .quickcheck(full_attack_2_test::<g_z_18446744073709551557, 555, 18446744073709551557u128> as fn() -> bool)
// }
