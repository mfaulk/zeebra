/*
 * Runs one univariate primitive with FLINT on a job file and times the call alone (#1206).
 *
 * Written against FLINT's documented public API only; no FLINT source is copied. FLINT is
 * LGPL-3.0 and is reached by dynamic linking from this separate executable, never from Zeebra.
 *
 *   flint-primitives-driver <job> <reps> [<out>]
 *   flint-primitives-driver --version
 *
 * The job format and the output format are in README.md beside this file. A modulus that fits a
 * machine word goes to nmod_poly, a wider one to fmpz_mod_poly. stdout gets `time_ns <median>`
 * and `min_ns <min>` over <reps> calls; a primitive this build has no entry point for prints
 * `unsupported` and exits 3.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <gmp.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_factor.h>
#include <flint/fmpz_mod.h>
#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

#ifndef DRIVER_CFLAGS
#define DRIVER_CFLAGS "unknown"
#endif

#define MAX_OPERANDS 3

static void die(const char *message)
{
    fprintf(stderr, "flint-primitives-driver: %s\n", message);
    exit(2);
}

static long long now_ns(void)
{
    struct timespec t;
#ifdef __APPLE__
    /* macOS's CLOCK_MONOTONIC ticks in microseconds; the raw clock is nanosecond-resolution. */
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
#else
    clock_gettime(CLOCK_MONOTONIC, &t);
#endif
    return (long long) t.tv_sec * 1000000000LL + t.tv_nsec;
}

static void read_fmpz(FILE *in, fmpz_t out)
{
    char buffer[512];
    if (fscanf(in, "%511s", buffer) != 1)
        die("truncated input");
    if (fmpz_set_str(out, buffer, 10) != 0)
        die("a residue is not a decimal integer");
}

static int compare_ll(const void *a, const void *b)
{
    long long x = *(const long long *) a, y = *(const long long *) b;
    return (x > y) - (x < y);
}

static void report(long long *times, int reps)
{
    qsort(times, (size_t) reps, sizeof *times, compare_ll);
    printf("time_ns %lld\nmin_ns %lld\n", times[reps / 2], times[0]);
}

struct job
{
    fmpz_t modulus;
    char primitive[32];
    int count;
    fmpz *vec[MAX_OPERANDS];
    slong len[MAX_OPERANDS];
};

static void read_job(const char *path, struct job *job)
{
    char keyword[32];
    FILE *in = fopen(path, "r");
    if (in == NULL)
        die("cannot open the job file");
    fmpz_init(job->modulus);
    if (fscanf(in, "%31s", keyword) != 1 || strcmp(keyword, "modulus") != 0)
        die("first line must be `modulus <p>`");
    read_fmpz(in, job->modulus);
    if (fscanf(in, "%31s %31s", keyword, job->primitive) != 2 || strcmp(keyword, "primitive") != 0)
        die("second line must be `primitive <name>`");
    job->count = 0;
    while (fscanf(in, "%31s", keyword) == 1)
    {
        long len = 0;
        slong i;
        if (strcmp(keyword, "vec") != 0 || fscanf(in, "%ld", &len) != 1 || len < 1)
            die("expected `vec <len>`");
        if (job->count == MAX_OPERANDS)
            die("too many operands");
        job->len[job->count] = len;
        job->vec[job->count] = _fmpz_vec_init(len);
        for (i = 0; i < len; i++)
            read_fmpz(in, job->vec[job->count] + i);
        job->count++;
    }
    fclose(in);
}

/* ---- word-size moduli: nmod_poly ---------------------------------------------------------- */

static void nmod_from(nmod_poly_t p, const struct job *job, int k)
{
    slong i;
    for (i = 0; i < job->len[k]; i++)
        nmod_poly_set_coeff_ui(p, i, fmpz_get_ui(job->vec[k] + i));
}

static void nmod_line(FILE *out, const nmod_poly_t p)
{
    slong i;
    for (i = 0; i < nmod_poly_length(p); i++)
        fprintf(out, i == 0 ? "%lu" : " %lu", (unsigned long) nmod_poly_get_coeff_ui(p, i));
    fputc('\n', out);
}

static void nmod_values(FILE *out, const ulong *v, slong n)
{
    slong i;
    for (i = 0; i < n; i++)
        fprintf(out, i == 0 ? "%lu" : " %lu", (unsigned long) v[i]);
    fputc('\n', out);
}

static int run_nmod(const struct job *job, int reps, FILE *out)
{
    ulong p = fmpz_get_ui(job->modulus);
    const char *name = job->primitive;
    nmod_poly_t a, b, c, r1, r2, r3;
    ulong *xs = NULL, *ys = NULL, scalar = 0;
    nmod_poly_factor_t factors;
    long long *times = malloc(sizeof(long long) * (size_t) reps);
    slong n = 0, i;
    int rep;

    nmod_poly_init(a, p);
    nmod_poly_init(b, p);
    nmod_poly_init(c, p);
    nmod_poly_init(r1, p);
    nmod_poly_init(r2, p);
    nmod_poly_init(r3, p);
    nmod_poly_factor_init(factors);

    if (strcmp(name, "interpolate") == 0)
    {
        n = job->len[0];
        xs = malloc(sizeof(ulong) * (size_t) n);
        ys = malloc(sizeof(ulong) * (size_t) n);
        for (i = 0; i < n; i++)
        {
            xs[i] = fmpz_get_ui(job->vec[0] + i);
            ys[i] = fmpz_get_ui(job->vec[1] + i);
        }
    }
    else
    {
        nmod_from(a, job, 0);
        if (job->count > 1 && strcmp(name, "multieval") != 0)
            nmod_from(b, job, 1);
        if (job->count > 2)
            nmod_from(c, job, 2);
        if (strcmp(name, "multieval") == 0)
        {
            n = job->len[1];
            xs = malloc(sizeof(ulong) * (size_t) n);
            ys = malloc(sizeof(ulong) * (size_t) n);
            for (i = 0; i < n; i++)
                xs[i] = fmpz_get_ui(job->vec[1] + i);
        }
    }

    for (rep = 0; rep < reps; rep++)
    {
        long long start = now_ns();
        if (strcmp(name, "mul") == 0 || strcmp(name, "mulfft") == 0)
            nmod_poly_mul(r1, a, b);
        else if (strcmp(name, "divrem") == 0)
            nmod_poly_divrem(r1, r2, a, b);
        else if (strcmp(name, "gcd") == 0)
            nmod_poly_gcd(r1, a, b);
        else if (strcmp(name, "xgcd") == 0)
            nmod_poly_xgcd(r1, r2, r3, a, b);
        else if (strcmp(name, "powmod") == 0)
        {
            /* The inverse of the reversed modulus is part of the call: Zeebra builds its own. */
            nmod_poly_reverse(r2, a, nmod_poly_length(a));
            nmod_poly_inv_series(r2, r2, nmod_poly_length(a));
            nmod_poly_powmod_x_fmpz_preinv(r1, (fmpz *) job->modulus, a, r2);
        }
        else if (strcmp(name, "roots") == 0)
            nmod_poly_roots(factors, a, 0);
        else if (strcmp(name, "multieval") == 0)
            nmod_poly_evaluate_nmod_vec_fast(ys, a, xs, n);
        else if (strcmp(name, "interpolate") == 0)
            nmod_poly_interpolate_nmod_vec_fast(r1, xs, ys, n);
        else if (strcmp(name, "compose") == 0)
            nmod_poly_compose_mod(r1, a, b, c);
        else if (strcmp(name, "resultant") == 0)
            scalar = nmod_poly_resultant(a, b);
        else
            die("unknown primitive");
        times[rep] = now_ns() - start;
    }
    report(times, reps);

    if (out != NULL)
    {
        if (strcmp(name, "divrem") == 0)
        {
            nmod_line(out, r1);
            nmod_line(out, r2);
        }
        else if (strcmp(name, "xgcd") == 0)
        {
            nmod_line(out, r1);
            nmod_line(out, r2);
            nmod_line(out, r3);
        }
        else if (strcmp(name, "roots") == 0)
        {
            /* Each factor is x - r, monic, so the root is the negated constant term. */
            for (i = 0; i < factors->num; i++)
            {
                ulong constant = nmod_poly_get_coeff_ui(factors->p + i, 0);
                fprintf(out, "%lu\n", (unsigned long) (constant == 0 ? 0 : p - constant));
            }
        }
        else if (strcmp(name, "multieval") == 0)
            nmod_values(out, ys, n);
        else if (strcmp(name, "resultant") == 0)
            fprintf(out, "%lu\n", (unsigned long) scalar);
        else
            nmod_line(out, r1);
    }

    free(times);
    free(xs);
    free(ys);
    nmod_poly_factor_clear(factors);
    nmod_poly_clear(a);
    nmod_poly_clear(b);
    nmod_poly_clear(c);
    nmod_poly_clear(r1);
    nmod_poly_clear(r2);
    nmod_poly_clear(r3);
    return 0;
}

/* ---- wide moduli: fmpz_mod_poly ----------------------------------------------------------- */

static void fmpz_mod_from(fmpz_mod_poly_t p, const struct job *job, int k, const fmpz_mod_ctx_t ctx)
{
    slong i;
    for (i = 0; i < job->len[k]; i++)
        fmpz_mod_poly_set_coeff_fmpz(p, i, job->vec[k] + i, ctx);
}

static void fmpz_mod_line(FILE *out, const fmpz_mod_poly_t p, const fmpz_mod_ctx_t ctx)
{
    slong i;
    fmpz_t c;
    fmpz_init(c);
    for (i = 0; i < fmpz_mod_poly_length(p, ctx); i++)
    {
        if (i > 0)
            fputc(' ', out);
        fmpz_mod_poly_get_coeff_fmpz(c, p, i, ctx);
        fmpz_fprint(out, c);
    }
    fputc('\n', out);
    fmpz_clear(c);
}

static int run_fmpz_mod(const struct job *job, int reps, FILE *out)
{
    const char *name = job->primitive;
    fmpz_mod_ctx_t ctx;
    fmpz_mod_poly_t a, b, c, r1, r2, r3;
    fmpz_mod_poly_factor_t factors;
    fmpz *ys = NULL;
    fmpz_t scalar;
    long long *times = malloc(sizeof(long long) * (size_t) reps);
    slong n = 0, i;
    int rep;

    if (strcmp(name, "interpolate") == 0)
    {
        /* FLINT 3.6 has no fast interpolation over fmpz_mod_poly in its public API. */
        printf("unsupported\n");
        free(times);
        return 3;
    }

    fmpz_mod_ctx_init(ctx, job->modulus);
    fmpz_mod_poly_init(a, ctx);
    fmpz_mod_poly_init(b, ctx);
    fmpz_mod_poly_init(c, ctx);
    fmpz_mod_poly_init(r1, ctx);
    fmpz_mod_poly_init(r2, ctx);
    fmpz_mod_poly_init(r3, ctx);
    fmpz_mod_poly_factor_init(factors, ctx);
    fmpz_init(scalar);

    fmpz_mod_from(a, job, 0, ctx);
    if (job->count > 1 && strcmp(name, "multieval") != 0)
        fmpz_mod_from(b, job, 1, ctx);
    if (job->count > 2)
        fmpz_mod_from(c, job, 2, ctx);
    if (strcmp(name, "multieval") == 0)
    {
        n = job->len[1];
        ys = _fmpz_vec_init(n);
    }

    for (rep = 0; rep < reps; rep++)
    {
        long long start = now_ns();
        if (strcmp(name, "mul") == 0 || strcmp(name, "mulfft") == 0)
            fmpz_mod_poly_mul(r1, a, b, ctx);
        else if (strcmp(name, "divrem") == 0)
            fmpz_mod_poly_divrem(r1, r2, a, b, ctx);
        else if (strcmp(name, "gcd") == 0)
            fmpz_mod_poly_gcd(r1, a, b, ctx);
        else if (strcmp(name, "xgcd") == 0)
            fmpz_mod_poly_xgcd(r1, r2, r3, a, b, ctx);
        else if (strcmp(name, "powmod") == 0)
        {
            slong len = fmpz_mod_poly_length(a, ctx);
            fmpz_mod_poly_reverse(r2, a, len, ctx);
            fmpz_mod_poly_inv_series(r2, r2, len, ctx);
            fmpz_mod_poly_powmod_x_fmpz_preinv(r1, job->modulus, a, r2, ctx);
        }
        else if (strcmp(name, "roots") == 0)
            fmpz_mod_poly_roots(factors, a, 0, ctx);
        else if (strcmp(name, "multieval") == 0)
            fmpz_mod_poly_evaluate_fmpz_vec_fast(ys, a, job->vec[1], n, ctx);
        else if (strcmp(name, "compose") == 0)
            fmpz_mod_poly_compose_mod(r1, a, b, c, ctx);
        else if (strcmp(name, "resultant") == 0)
            fmpz_mod_poly_resultant(scalar, a, b, ctx);
        else
            die("unknown primitive");
        times[rep] = now_ns() - start;
    }
    report(times, reps);

    if (out != NULL)
    {
        if (strcmp(name, "divrem") == 0)
        {
            fmpz_mod_line(out, r1, ctx);
            fmpz_mod_line(out, r2, ctx);
        }
        else if (strcmp(name, "xgcd") == 0)
        {
            fmpz_mod_line(out, r1, ctx);
            fmpz_mod_line(out, r2, ctx);
            fmpz_mod_line(out, r3, ctx);
        }
        else if (strcmp(name, "roots") == 0)
        {
            fmpz_t root;
            fmpz_init(root);
            for (i = 0; i < factors->num; i++)
            {
                fmpz_mod_poly_get_coeff_fmpz(root, factors->poly + i, 0, ctx);
                fmpz_mod_neg(root, root, ctx);
                fmpz_fprint(out, root);
                fputc('\n', out);
            }
            fmpz_clear(root);
        }
        else if (strcmp(name, "multieval") == 0)
        {
            for (i = 0; i < n; i++)
            {
                if (i > 0)
                    fputc(' ', out);
                fmpz_fprint(out, ys + i);
            }
            fputc('\n', out);
        }
        else if (strcmp(name, "resultant") == 0)
        {
            fmpz_fprint(out, scalar);
            fputc('\n', out);
        }
        else
            fmpz_mod_line(out, r1, ctx);
    }

    free(times);
    if (ys != NULL)
        _fmpz_vec_clear(ys, n);
    fmpz_clear(scalar);
    fmpz_mod_poly_factor_clear(factors, ctx);
    fmpz_mod_poly_clear(a, ctx);
    fmpz_mod_poly_clear(b, ctx);
    fmpz_mod_poly_clear(c, ctx);
    fmpz_mod_poly_clear(r1, ctx);
    fmpz_mod_poly_clear(r2, ctx);
    fmpz_mod_poly_clear(r3, ctx);
    fmpz_mod_ctx_clear(ctx);
    return 0;
}

int main(int argc, char **argv)
{
    struct job job;
    FILE *out = NULL;
    int reps, status, k;

    if (argc == 2 && strcmp(argv[1], "--version") == 0)
    {
        printf("flint-primitives-driver contract 1\n");
        printf("flint %s (headers %s), gmp %s\n", flint_version, FLINT_VERSION, gmp_version);
        printf("driver cflags: %s\n", DRIVER_CFLAGS);
        printf("flint threads: %d\n", flint_get_num_threads());
        return 0;
    }
    if (argc < 3 || argc > 4)
        die("usage: flint-primitives-driver <job> <reps> [<out>]");
    reps = atoi(argv[2]);
    if (reps < 1)
        die("reps must be at least 1");
    read_job(argv[1], &job);
    if (argc == 4)
    {
        out = fopen(argv[3], "w");
        if (out == NULL)
            die("cannot open the output file");
    }

    if (fmpz_abs_fits_ui(job.modulus))
        status = run_nmod(&job, reps, out);
    else
        status = run_fmpz_mod(&job, reps, out);

    if (out != NULL)
        fclose(out);
    for (k = 0; k < job.count; k++)
        _fmpz_vec_clear(job.vec[k], job.len[k]);
    fmpz_clear(job.modulus);
    flint_cleanup_master();
    return status;
}
