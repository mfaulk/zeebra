/*
 * Factors one univariate polynomial with FLINT, timing the factorization call alone (#784).
 *
 * Written against FLINT's documented public API only; no FLINT source is copied. FLINT is
 * LGPL-3.0 and is reached by dynamic linking from this separate executable, never from Zeebra.
 *
 *   flint-factor-driver [--algorithm default|cz|ks|berlekamp] <in.poly> [<out.factors>]
 *   flint-factor-driver --version
 *
 * <in.poly> is `modulus <p>`, `degree <n>`, then n + 1 decimal coefficients low to high. A
 * modulus that fits a machine word goes to nmod_poly, a wider one to fmpz_mod_poly. stdout gets
 * `time_ns <t>`; <out.factors> gets one line per monic factor, `<multiplicity> <c0> ... <cd>`,
 * unsorted (the harness sorts both sides).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <gmp.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_factor.h>
#include <flint/fmpz_mod.h>
#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

#ifndef DRIVER_CFLAGS
#define DRIVER_CFLAGS "unknown"
#endif

enum algorithm { ALG_DEFAULT, ALG_CZ, ALG_KS, ALG_BERLEKAMP };

static const char *const ALGORITHM_NAMES[] = {"default", "cz", "ks", "berlekamp"};

static void die(const char *message)
{
    fprintf(stderr, "flint-factor-driver: %s\n", message);
    exit(2);
}

static long long now_ns(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (long long) t.tv_sec * 1000000000LL + t.tv_nsec;
}

/* Reads one whitespace-delimited decimal token into `out`. */
static void read_fmpz(FILE *in, fmpz_t out)
{
    char buffer[512];
    if (fscanf(in, "%511s", buffer) != 1)
        die("truncated input");
    if (fmpz_set_str(out, buffer, 10) != 0)
        die("a coefficient is not a decimal integer");
}

static FILE *open_out(const char *path)
{
    FILE *out;
    if (path == NULL)
        return NULL;
    out = fopen(path, "w");
    if (out == NULL)
        die("cannot open the output file");
    return out;
}

static void factor_nmod(FILE *in, const fmpz_t modulus, slong degree, enum algorithm alg,
                        const char *out_path)
{
    nmod_poly_t f;
    nmod_poly_factor_t factors;
    fmpz_t c;
    long long start, elapsed;
    slong i, j;
    FILE *out;

    nmod_poly_init(f, fmpz_get_ui(modulus));
    fmpz_init(c);
    for (i = 0; i <= degree; i++)
    {
        read_fmpz(in, c);
        nmod_poly_set_coeff_ui(f, i, fmpz_get_ui(c));
    }
    nmod_poly_factor_init(factors);

    start = now_ns();
    switch (alg)
    {
        case ALG_DEFAULT: nmod_poly_factor(factors, f); break;
        case ALG_CZ: nmod_poly_factor_with_cantor_zassenhaus(factors, f); break;
        case ALG_KS: nmod_poly_factor_with_kaltofen_shoup(factors, f); break;
        case ALG_BERLEKAMP: nmod_poly_factor_with_berlekamp(factors, f); break;
    }
    elapsed = now_ns() - start;
    printf("time_ns %lld\n", elapsed);

    out = open_out(out_path);
    if (out != NULL)
    {
        for (i = 0; i < factors->num; i++)
        {
            fprintf(out, "%ld", (long) factors->exp[i]);
            for (j = 0; j < nmod_poly_length(factors->p + i); j++)
                fprintf(out, " %lu", (unsigned long) nmod_poly_get_coeff_ui(factors->p + i, j));
            fputc('\n', out);
        }
        fclose(out);
    }

    nmod_poly_factor_clear(factors);
    nmod_poly_clear(f);
    fmpz_clear(c);
}

static void factor_fmpz_mod(FILE *in, const fmpz_t modulus, slong degree, enum algorithm alg,
                            const char *out_path)
{
    fmpz_mod_ctx_t ctx;
    fmpz_mod_poly_t f;
    fmpz_mod_poly_factor_t factors;
    fmpz_t c;
    long long start, elapsed;
    slong i, j;
    FILE *out;

    fmpz_mod_ctx_init(ctx, modulus);
    fmpz_mod_poly_init(f, ctx);
    fmpz_init(c);
    for (i = 0; i <= degree; i++)
    {
        read_fmpz(in, c);
        fmpz_mod_poly_set_coeff_fmpz(f, i, c, ctx);
    }
    fmpz_mod_poly_factor_init(factors, ctx);

    start = now_ns();
    switch (alg)
    {
        case ALG_DEFAULT: fmpz_mod_poly_factor(factors, f, ctx); break;
        case ALG_CZ: fmpz_mod_poly_factor_cantor_zassenhaus(factors, f, ctx); break;
        case ALG_KS: fmpz_mod_poly_factor_kaltofen_shoup(factors, f, ctx); break;
        case ALG_BERLEKAMP: fmpz_mod_poly_factor_berlekamp(factors, f, ctx); break;
    }
    elapsed = now_ns() - start;
    printf("time_ns %lld\n", elapsed);

    out = open_out(out_path);
    if (out != NULL)
    {
        for (i = 0; i < factors->num; i++)
        {
            fprintf(out, "%ld", (long) factors->exp[i]);
            for (j = 0; j < fmpz_mod_poly_length(factors->poly + i, ctx); j++)
            {
                fmpz_mod_poly_get_coeff_fmpz(c, factors->poly + i, j, ctx);
                fputc(' ', out);
                fmpz_fprint(out, c);
            }
            fputc('\n', out);
        }
        fclose(out);
    }

    fmpz_mod_poly_factor_clear(factors, ctx);
    fmpz_mod_poly_clear(f, ctx);
    fmpz_mod_ctx_clear(ctx);
    fmpz_clear(c);
}

int main(int argc, char **argv)
{
    enum algorithm alg = ALG_DEFAULT;
    const char *in_path = NULL, *out_path = NULL;
    char keyword[32];
    long degree;
    fmpz_t modulus;
    FILE *in;
    int arg = 1;

    if (argc == 2 && strcmp(argv[1], "--version") == 0)
    {
        printf("flint-factor-driver contract 1\n");
        printf("flint %s (headers %s), gmp %s\n", flint_version, FLINT_VERSION, gmp_version);
        printf("driver cflags: %s\n", DRIVER_CFLAGS);
        printf("flint threads: %d\n", flint_get_num_threads());
        return 0;
    }
    if (arg + 1 < argc && strcmp(argv[arg], "--algorithm") == 0)
    {
        int k, found = 0;
        for (k = 0; k < 4; k++)
            if (strcmp(argv[arg + 1], ALGORITHM_NAMES[k]) == 0)
            {
                alg = (enum algorithm) k;
                found = 1;
            }
        if (!found)
            die("--algorithm takes default, cz, ks or berlekamp");
        arg += 2;
    }
    if (arg >= argc || argc - arg > 2)
        die("usage: flint-factor-driver [--algorithm default|cz|ks|berlekamp] <in.poly> [<out>]");
    in_path = argv[arg];
    if (arg + 1 < argc)
        out_path = argv[arg + 1];

    in = fopen(in_path, "r");
    if (in == NULL)
        die("cannot open the input file");
    fmpz_init(modulus);
    if (fscanf(in, "%31s", keyword) != 1 || strcmp(keyword, "modulus") != 0)
        die("first line must be `modulus <p>`");
    read_fmpz(in, modulus);
    if (fscanf(in, "%31s %ld", keyword, &degree) != 2 || strcmp(keyword, "degree") != 0
        || degree < 1)
        die("second line must be `degree <n>` with n >= 1");

    if (fmpz_abs_fits_ui(modulus))
        factor_nmod(in, modulus, degree, alg, out_path);
    else
        factor_fmpz_mod(in, modulus, degree, alg, out_path);

    fclose(in);
    fmpz_clear(modulus);
    flint_cleanup_master();
    return 0;
}
