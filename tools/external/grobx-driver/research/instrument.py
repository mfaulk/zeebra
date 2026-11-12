#!/usr/bin/env python3
"""Apply passive counters only to the explicitly pinned GPL engine in a private workspace."""
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
PIN = '1854835dbc25f24dc9a9ba017024d5030e99da1c'
HASHES = {
    'src/lib.rs': '6bfba24797a59f060edafb583ef4ee57cbea0765c678d5a1193348029ead4368',
    'src/field.rs': '1ee9e9012c7ff486a9d4327eb7859245c9ab726b4c9365c78132e6fe10cad321',
    'src/matrix.rs': '04dc645efe2bcedcbc2ba827c8b075aba8327ad5f7225161a736d1f848bc3cf3',
    'src/budget.rs': 'ffb60d3e83dd27af697c5b8b945c2eadd1468326e712101c80984f4b401b010b',
}


def replace(source, old, new, expected=1):
    if source.count(old) != expected:
        raise ValueError(f'pinned source anchor changed: {old[:75]!r}')
    return source.replace(old, new)


def instrument(root):
    root = Path(root)
    for name, digest in HASHES.items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'pinned source differs: {name}')
    lib = root / 'src/lib.rs'
    lib.write_text(lib.read_text() + '\npub mod research_work;\n')
    (root / 'src/research_work.rs').write_text((HERE / 'work.rs').read_text())
    cargo = root / 'Cargo.toml'
    cargo.write_text(replace(cargo.read_text(), '[dependencies]\n', '[dependencies]\nserde_json = "1"\n'))
    field = root / 'src/field.rs'
    s = field.read_text()
    anchors = {
        '    unsafe fn load(&self, dense: &mut [i64], cols: &[MonoId], coefs: &[u32]) {':
            '        crate::research_work::load(cols.len());',
        '    unsafe fn sub_mul(&self, dense: &mut [i64], cols: &[MonoId], coefs: &[u32], c: u32) {':
            '        crate::research_work::products(cols.len(), 1, usize::from(c != 0));',
        '    fn take(&self, entry: &mut i64) -> u32 {': '        crate::research_work::take();',
        '    fn mul(&self, a: u32, b: u32) -> u32 {': '        crate::research_work::direct_mul();',
        '    unsafe fn load_band(&self, band: &mut [[i64; BAND]], k: usize, cols: &[MonoId], coefs: &[u32]) {':
            '        crate::research_work::load(cols.len());',
    }
    for anchor, code in anchors.items():
        s = replace(s, anchor, anchor + '\n' + code)
    # Restrict edits to Gf31's band entry points, before the helper kernels.
    start = s.index('impl Field for Gf31 {')
    end = s.index('unsafe fn sub_mul_band_sse2(')
    prefix, body, suffix = s[:start], s[start:end], s[end:]
    body = replace(body, '        c: &[u32; BAND],\n    ) {\n        debug_assert_eq!(cols.len(), coefs.len());',
        '        c: &[u32; BAND],\n    ) {\n        crate::research_work::products(cols.len(), BAND, c.iter().filter(|&&x| x != 0).count());\n        debug_assert_eq!(cols.len(), coefs.len());')
    body = replace(body, '        c: u32,\n    ) {\n        debug_assert_eq!(cols.len(), coefs.len());',
        '        c: u32,\n    ) {\n        crate::research_work::products(cols.len(), 1, usize::from(c != 0));\n        debug_assert_eq!(cols.len(), coefs.len());')
    field.write_text(prefix + body + suffix)
    budget = root / 'src/budget.rs'
    s = budget.read_text()
    s = replace(s, '        self.subtracted += units as u64;',
        '        crate::research_work::subtraction(units);\n        self.subtracted += units as u64;')
    budget.write_text(s)
    matrix = root / 'src/matrix.rs'
    s = matrix.read_text()
    s = replace(s, '        red\n    }\n\n    // row-scan-time.8',
        '        crate::research_work::begin(matrix.rows.len(), matrix.given, matrix.columns(), matrix.cols.len());\n        red.research_snapshot(None);\n        red\n    }\n\n    // row-scan-time.8')
    sample = '''    fn research_snapshot(&self, extra: Option<&Reduced<F>>) {
        if !crate::research_work::enabled() { return; }
        let ci = std::mem::size_of::<MonoId>();
        let cv = std::mem::size_of::<F::Coef>();
        let made_entries = self.made.iter().map(|r| r.cols.len()).sum();
        let made_capacity = self.made.iter().map(|r| r.cols.capacity() * ci + r.coefs.capacity() * cv).sum();
        let workspace_entries = self.row_cols.len() + self.band_cols.iter().map(Vec::len).sum::<usize>();
        let workspace_capacity = self.dense.capacity() * std::mem::size_of::<F::Acc>()
            + self.band.capacity() * std::mem::size_of::<[F::Acc; BAND]>()
            + self.row_cols.capacity() * ci + self.row_coefs.capacity() * cv
            + self.band_cols.iter().map(|v| v.capacity() * ci).sum::<usize>()
            + self.band_coefs.iter().map(|v| v.capacity() * cv).sum::<usize>()
            + self.marks.capacity() * std::mem::size_of::<u64>();
        crate::research_work::memory(self.matrix.cols.len(), self.matrix.cols.capacity() * ci,
            made_entries, made_capacity, workspace_entries, workspace_capacity,
            extra.map_or(0, |r| r.cols.len()),
            extra.map_or(0, |r| r.cols.capacity() * ci + r.coefs.capacity() * cv));
    }

'''
    s = replace(s, '    pub(crate) fn give_back(&mut self, bufs: &mut Buffers<F>) {',
        sample + '    pub(crate) fn give_back(&mut self, bufs: &mut Buffers<F>) {\n        self.research_snapshot(None);\n        crate::research_work::end();')
    s = replace(s, '        self.row_coefs = std::mem::replace(&mut out.coefs, coefs);\n        out',
        '        self.row_coefs = std::mem::replace(&mut out.coefs, coefs);\n        self.research_snapshot(Some(&out));\n        out')
    s = replace(s, '        self.band_coefs[k] = std::mem::replace(&mut out.coefs, coefs);\n        out',
        '        self.band_coefs[k] = std::mem::replace(&mut out.coefs, coefs);\n        self.research_snapshot(Some(&out));\n        out')
    s = replace(s, '        self.made.push(row);\n        true',
        '        self.made.push(row);\n        self.research_snapshot(None);\n        true')
    # Phase labels alter no seed, reducer, pivot, scan, band or cofactor state.
    s = replace(s, '    fn add(&mut self, r: RowId, k: F::Coef, budget: &mut Budget) -> Result<(), Stop> {',
        '    fn add(&mut self, r: RowId, k: F::Coef, budget: &mut Budget) -> Result<(), Stop> {\n        crate::research_work::phase(2);')
    s = replace(s, '        budget.spend_added(cols.len())',
        '        let result = budget.spend_added(cols.len());\n        crate::research_work::phase(0);\n        result')
    s = replace(s, '        budget.spend_added(BAND * cols.len())',
        '        let result = budget.spend_added(BAND * cols.len());\n        crate::research_work::phase(0);\n        result')
    band_start = s.index('    pub(crate) fn add_band(')
    band_end = s.index('    fn reduce_band_loaded(', band_start)
    body = s[band_start:band_end]
    body = replace(body, '        debug_assert!(F::BANDS, "a field with bands");',
        '        crate::research_work::phase(2);\n        debug_assert!(F::BANDS, "a field with bands");')
    s = s[:band_start] + body + s[band_end:]
    s = replace(s, '        let mut by_lead: Vec<MadeId> = (0..self.made.len()).map(MadeId::at).collect();',
        '        crate::research_work::phase(1);\n        let mut by_lead: Vec<MadeId> = (0..self.made.len()).map(MadeId::at).collect();')
    matrix.write_text(s)
