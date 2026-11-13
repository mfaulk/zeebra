use std::time::Instant;
use zeebra::{
    grobner::{
        f4::{
            macaulay::MacaulayMatrix,
            structured::{eliminate_to, BlockOutcome, BlockPlan, RowForm},
            symbolic::MonicBasis,
            BatchObserver,
        },
        pairs::CriticalPair,
        F4Options,
    },
    linalg::{selective, sparse::back_substitute_pivots_within},
    util::Json,
    FiniteField,
};

pub struct Observer<'a> {
    pub mode: &'a str,
    pub detailed: bool,
    pub batches: Vec<Json>,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Observer<'_> {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {}

    fn eliminate(
        &mut self,
        matrix: &mut MacaulayMatrix<N, F>,
        options: &F4Options,
    ) -> Option<Result<BlockOutcome, usize>> {
        assert!(options.reduce_batch_rows);
        let mut input_leads = vec![false; matrix.num_columns()];
        for row in matrix.matrix().rows() {
            if let Some(c) = row.leading_column() {
                input_leads[c] = true;
            }
        }
        let digest = self
            .detailed
            .then(|| zeebra::grobner::f4::matrix_corpus::digest_of(matrix));
        let allowance = options.live_entry_allowance::<F>();
        let start = Instant::now();
        let mut block = match eliminate_to(
            BlockPlan::ReducersFirstBlock,
            RowForm::Echelon,
            options.elimination,
            matrix,
            allowance,
        ) {
            Ok(block) => block,
            Err(n) => return Some(Err(n)),
        };
        let forward = start.elapsed();
        let selected: Vec<_> = matrix
            .matrix()
            .rows()
            .iter()
            .map(|row| {
                row.leading_column()
                    .is_some_and(|c| self.mode == "dense-all" || !input_leads[c])
            })
            .collect();
        let start = Instant::now();
        let mut details = Json::Null;
        let visits = if self.mode == "full" {
            match back_substitute_pivots_within(
                matrix.matrix_mut(),
                allowance,
                &mut block.statistics,
            ) {
                Ok(n) => n,
                Err(n) => return Some(Err(n)),
            }
        } else {
            let r = match selective::reduce(
                matrix.matrix_mut(),
                &selected,
                allowance,
                64 * 1024 * 1024,
                &mut block.statistics,
            ) {
                Ok(report) => report,
                Err(selective::Error::Entries(n)) => return Some(Err(n)),
                Err(error) => panic!("selective research refusal: {error:?}"),
            };
            details = self::details(&r);
            r.targets
        };
        let backward = start.elapsed();
        block.back_substituted_rows = Some(visits);
        self.batches.push(Json::object([
            ("rows", Json::size(matrix.num_rows())),
            ("columns", Json::size(matrix.num_columns())),
            ("forward_ns", Json::nanos(forward)),
            ("backward_ns", Json::nanos(backward)),
            (
                "input_matrix_digest",
                digest.map_or(Json::Null, Json::string),
            ),
            ("details", details),
        ]));
        Some(Ok(block))
    }
}

pub fn details(r: &selective::Report) -> Json {
    Json::object([
        ("targets", Json::size(r.targets)),
        ("products", Json::size(r.products)),
        ("scans", Json::size(r.scans)),
        ("loads", Json::size(r.loads)),
        ("gathers", Json::size(r.gathers)),
        ("workspace_bytes", Json::size(r.workspace_bytes)),
        ("peak_entries", Json::size(r.peak_entries)),
        ("peak_capacity_entries", Json::size(r.peak_capacity_entries)),
    ])
}
