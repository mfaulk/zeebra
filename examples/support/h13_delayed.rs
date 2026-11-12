// Canonical residues are recovered before pivot decisions and support-count changes.
#[derive(Clone, Debug)]
pub struct Delayed<const P: u64> {
    cells: Vec<u64>,
    nonzeros: usize,
    lead: usize,
    dirty_lead: usize,
    tail: usize,
    remaining: u64,
    interval: u64,
}

impl<const P: u64> Delayed<P> {
    pub const fn headroom() -> u64 {
        ((u64::MAX as u128 - (P - 1) as u128) / ((P - 1) as u128 * (P - 1) as u128)) as u64
    }

    pub fn new(width: usize) -> Self {
        assert!(P > 1 && P <= u32::MAX as u64);
        assert!(Self::headroom() > 0);
        Self {
            cells: vec![0; width],
            nonzeros: 0,
            lead: width,
            dirty_lead: width,
            tail: 0,
            remaining: Self::headroom(),
            interval: Self::headroom(),
        }
    }

    pub fn load(&mut self, entries: impl IntoIterator<Item = (usize, u64)>) {
        assert_eq!(self.nonzeros, 0);
        for (column, value) in entries {
            assert!(value > 0 && value < P);
            self.cells[column] = value;
            self.nonzeros += 1;
            self.lead = self.lead.min(column);
            self.dirty_lead = self.dirty_lead.min(column);
            self.tail = self.tail.max(column + 1);
        }
        self.remaining = self.interval;
    }

    pub fn nonzeros(&self) -> usize {
        self.nonzeros
    }

    pub fn leading(&mut self) -> Option<(usize, u64)> {
        if self.nonzeros == 0 {
            return None;
        }
        while self.cells[self.lead].is_multiple_of(P) {
            self.lead += 1;
        }
        Some((self.lead, self.cells[self.lead] % P))
    }

    pub fn subtract(&mut self, columns: &[usize], coefficients: &[u16], factor: u64) {
        assert_eq!(columns.len(), coefficients.len());
        assert!(P <= u16::MAX as u64 && factor < P);
        if factor == 0 || columns.is_empty() {
            return;
        }
        if self.remaining == 0 {
            for cell in &mut self.cells[self.dirty_lead..self.tail] {
                *cell %= P;
            }
            self.remaining = self.interval;
        }
        let negative = P - factor;
        for (&column, &coefficient) in columns.iter().zip(coefficients) {
            debug_assert!(coefficient > 0 && (coefficient as u64) < P);
            let before = self.cells[column];
            let after = before + negative * coefficient as u64;
            self.cells[column] = after;
            self.nonzeros += usize::from(before.is_multiple_of(P));
            self.nonzeros -= usize::from(after.is_multiple_of(P));
        }
        self.remaining -= 1;
        self.lead = self.lead.min(columns[0]);
        self.dirty_lead = self.dirty_lead.min(columns[0]);
        self.tail = self.tail.max(columns[columns.len() - 1] + 1);
    }

    pub fn take(&mut self) -> Vec<(usize, u64)> {
        // Clear even modular zeros: delayed cells may contain nonzero multiples of P.
        let mut result = Vec::with_capacity(self.nonzeros);
        for column in self.dirty_lead..self.tail {
            let value = std::mem::take(&mut self.cells[column]) % P;
            if value != 0 {
                result.push((column, value));
            }
        }
        assert_eq!(result.len(), self.nonzeros);
        self.nonzeros = 0;
        self.lead = self.cells.len();
        self.dirty_lead = self.cells.len();
        self.tail = 0;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::Delayed;
    // Forced folds preserve exact arithmetic at maximal factors, including reactivated columns.
    #[test]
    fn forced_folds_match_a_canonical_reference() {
        let mut row = Delayed::<32003>::new(65);
        row.interval = 2;
        row.load([(0, 32002), (64, 1)]);
        let mut expected = vec![0u64; 65];
        expected[0] = 32002;
        expected[64] = 1;
        for i in 0..300 {
            let columns = [0, 31, 32, 63, 64];
            let values = [1u16, 32002, 123, 32001, 7];
            let factor = 1 + (i * 15991) % 32002;
            row.subtract(&columns, &values, factor);
            for (&column, &value) in columns.iter().zip(&values) {
                expected[column] = (expected[column] + (32003 - factor) * value as u64) % 32003;
            }
            assert_eq!(row.nonzeros(), expected.iter().filter(|&&x| x != 0).count());
            assert_eq!(
                row.leading(),
                expected
                    .iter()
                    .enumerate()
                    .find(|(_, x)| **x != 0)
                    .map(|(i, x)| (i, *x))
            );
        }
        let expected: Vec<_> = expected
            .into_iter()
            .enumerate()
            .filter(|(_, x)| *x != 0)
            .collect();
        assert_eq!(row.take(), expected);
        assert!(row.cells.iter().all(|&x| x == 0));
    }
    // Gathering clears delayed multiples skipped when the leading column advanced.
    #[test]
    fn take_clears_the_skipped_prefix() {
        let mut row = Delayed::<32003>::new(3);
        row.load([(0, 1), (2, 2)]);
        row.subtract(&[0], &[1], 1);
        assert_eq!(row.leading(), Some((2, 2)));
        row.take();
        assert!(row.cells.iter().all(|&x| x == 0));
    }
}
