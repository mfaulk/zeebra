#![allow(dead_code)]
#[path = "cryptanalysis/src/primitives/anemoi.rs"]
mod anemoi;
#[path = "cryptanalysis/src/attacks/anemoi_cico.rs"]
mod anemoi_cico;
#[path = "cryptanalysis/src/primitives/poseidon.rs"]
mod poseidon;
use anemoi::{Anemoi, AnemoiParameters};
use anemoi_cico::{AnemoiCico, AnemoiModel};
use zeebra::{fields::PrimeFieldElement64, FiniteField, KnownOrder, MultivariatePolynomial};
fn emit<const N: usize, F: KnownOrder>(name: &str, system: Vec<MultivariatePolynomial<N, F>>) {
    let names: Vec<_> = (0..N).map(|i| format!("x{i}")).collect();
    let mut output = format!("{}\n{}\n", names.join(","), F::order_limbs()[0]);
    for p in system {
        let mut terms: Vec<_> = p
            .terms()
            .iter()
            .map(|(m, c)| {
                let mut f = vec![format!("{c}")];
                for (i, e) in m.exponents().iter().enumerate() {
                    if *e > 0 {
                        f.push(format!("x{i}^{e}"));
                    }
                }
                f.join("*")
            })
            .collect();
        terms.sort();
        output.push_str(&terms.join("+"));
        output.push_str(",\n");
    }
    std::fs::write(
        std::path::Path::new(&std::env::args().nth(1).expect("output directory")).join(format!("{name}.system")),
        output,
    )
    .unwrap();
}
fn a<const N: usize>(rounds: usize, model: AnemoiModel, name: &str) {
    let a =
        Anemoi::<PrimeFieldElement64<65537>>::new(AnemoiParameters::six_worlds_at(65537, rounds))
            .unwrap();
    emit(name, AnemoiCico::new(a, model).system::<N>().unwrap());
}
fn main() {
    a::<8>(4, AnemoiModel::Fcico, "anemoi17-cico-n4-fcico");
    a::<5>(4, AnemoiModel::Pcico, "anemoi17-cico-n4-pcico");
    a::<10>(5, AnemoiModel::Fcico, "anemoi17-cico-n5-fcico");
    a::<6>(5, AnemoiModel::Pcico, "anemoi17-cico-n5-pcico");
    a::<7>(6, AnemoiModel::Pcico, "anemoi17-cico-n6-pcico");
    type K = PrimeFieldElement64<2130706433>;
    let p = poseidon::Poseidon::new(poseidon::PoseidonParameters {
        prime: 2130706433,
        alpha: 3,
        t: 16,
        r_f: 4,
        r_p: 2,
    })
    .unwrap();
    let c = poseidon::CicoInstance::new(
        p,
        2,
        vec![K::new(12623332), K::new(15622786), K::new(0), K::new(0)],
        None,
    )
    .unwrap();
    emit("poseidon31-cico-t16-rf4-rp2", c.system::<80>().unwrap());
}
