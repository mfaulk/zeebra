/// The `matrix!` macro enables easy construction of small matrices.

#[macro_export]
macro_rules! matrix {
    () => {
        {
            // Handle the case when called with no arguments, i.e. matrix![]
            use $crate::linalg::Matrix;
            Matrix::new(0, 0, &vec![])
        }
    };
    ($( $( $x: expr ),*);*) => {
        {
            use $crate::linalg::Matrix;
            let data_as_nested_array = [ $( [ $($x),* ] ),* ];
            let rows = data_as_nested_array.len();
            let cols = data_as_nested_array[0].len();
            let data_as_flat_array: Vec<_> = data_as_nested_array.into_iter()
                .flat_map(|row| row.into_iter())
                .collect();
            Matrix::new(rows, cols, &data_as_flat_array)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{FiniteField, Zp541},
        linalg::Matrix,
    };

    #[test]
    fn matrix_macro() {
        type F = Zp541;

        // An arbitrary rectangular matrix
        let m: Matrix<F> = matrix![F::new(1), F::new(2), F::new(3);
                          F::new(4), F::new(5), F::new(6)];
        assert_eq!(2, m.num_rows);
        assert_eq!(3, m.num_columns);

        let expected = Matrix::new(
            2,
            3,
            &vec![
                F::new(1),
                F::new(2),
                F::new(3),
                F::new(4),
                F::new(5),
                F::new(6),
            ],
        );
        assert_eq!(m, expected);
    }
}
