// ****************************************************************************
//  algebraic.cc                                                DB48X project
// ****************************************************************************
//
//   File Description:
//
//     Shared code for all algebraic commands
//
//
//
//
//
//
//
//
// ****************************************************************************
//   (C) 2022 Christophe de Dinechin <christophe@dinechin.org>
//   This software is licensed under the terms outlined in LICENSE.txt
// ****************************************************************************
//   This file is part of DB48X.
//
//   DB48X is free software: you can redistribute it and/or modify
//   it under the terms outlined in the LICENSE.txt file
//
//   DB48X is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// ****************************************************************************

#include "algebraic.h"

#include "arithmetic.h"
#include "factor.h"
#include "fraction.h"
#include "list.h"
#include "array.h"
#include "bignum.h"
#include "compare.h"
#include "complex.h"
#include "constants.h"
#include "decimal.h"
#include "equations.h"
#include "expression.h"
#include "functions.h"
#include "hwfp.h"
#include "integer.h"
#include "object.h"
#include "parser.h"
#include "range.h"
#include "renderer.h"
#include "runtime.h"
#include "settings.h"
#include "tag.h"
#include "unit.h"
#include "user_interface.h"

#include <cctype>
#include <cmath>
#include <cstdio>

using namespace eq_wildcards;


RECORDER(algebraic,       16, "RPL Algebraics");
RECORDER(algebraic_error, 16, "Errors processing a algebraic");
RECORDER(quotient,        16, "Quotient computations");

bool algebraic::in_expression = false;


INSERT_BODY(algebraic)
// ----------------------------------------------------------------------------
//   Enter data in algebraic mode
// ----------------------------------------------------------------------------
{
    return ui.insert_object(o, o->arity() ? ui.ALGEBRAIC : ui.CONSTANT);
}


bool algebraic::decimal_promotion(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to a decimal / floating-point type
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    id xt = x->type();
    record(algebraic, "Real promotion of %p from %+s to decimal",
           (object_p) x, object::name(xt));

    switch(xt)
    {
    case ID_hwfloat:
        if (algebraic_p xx = decimal::from(hwfloat_p(+x)->value()))
        {
            x = xx;
            return true;
        }
        break;
    case ID_hwdouble:
        if (algebraic_p xx = decimal::from(hwdouble_p(+x)->value()))
        {
            x = xx;
            return true;
        }
        break;
    case ID_decimal:
    case ID_neg_decimal:
        return true;

    case ID_integer:
    case ID_neg_integer:
        if (algebraic_p xx = decimal::from_integer(integer_p(+x)))
        {
            x = xx;
            return true;
        }
        break;
    case ID_bignum:
    case ID_neg_bignum:
        if (algebraic_p xx = decimal::from_bignum(bignum_p(+x)))
        {
            x = xx;
            return true;
        }
        break;
    case ID_fraction:
    case ID_neg_fraction:
        if (algebraic_p xx = decimal::from_fraction(fraction_p(+x)))
        {
            x = xx;
            return true;
        }
        break;
    case ID_big_fraction:
    case ID_neg_big_fraction:
        if (algebraic_p xx = decimal::from_big_fraction(big_fraction_p(+x)))
        {
            x = xx;
            return true;
        }
        break;
    default:
        break;
    }
    return false;
}

template<typename value>
algebraic_p algebraic::as_hwfp(value x)
// ----------------------------------------------------------------------------
//   Return a hardware floating-point value if possible
// ----------------------------------------------------------------------------
{
    if (Settings.HardwareFloatingPoint())
    {
        uint prec = Settings.Precision();
        if (prec <= 7)
            return hwfloat::make(float(x));
        if (prec <= 16)
            return hwdouble::make(double(x));
    }
    return nullptr;
}


bool algebraic::hwfp_promotion(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to a hardware floating-point type if possible
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    if (!Settings.HardwareFloatingPoint())
        return false;
    uint prec = Settings.Precision();
    if (prec > 16)
        return false;
    return prec > 7 ? to_hwdouble(x) : to_hwfloat(x);
}


bool algebraic::complex_promotion(algebraic_g &x, object::id type)
// ----------------------------------------------------------------------------
//   Promote the value x to the given complex type
// ----------------------------------------------------------------------------
{
    id xt = x->type();
    if (xt == type)
        return true;

    record(algebraic, "Complex promotion of %p from %+s to %+s",
           (object_p) x, object::name(xt), object::name(type));

    if (!is_complex(type))
    {
        record(algebraic_error, "Complex promotion to invalid type %+s",
               object::name(type));
        return false;
    }

    if (xt == ID_polar)
    {
        // Convert from polar to rectangular
        polar_g z = polar_p(algebraic_p(x));
        x = rectangular_p(z->as_rectangular());
        return +x;
    }
    else if (xt == ID_rectangular)
    {
        // Convert from rectangular to polar
        rectangular_g z = rectangular_p(algebraic_p(x));
        x = polar_p(z->as_polar());
        return +x;
    }
    else if (is_symbolic(xt))
    {
        // Assume a symbolic value is complex for now
        // TODO: Implement `REALASSUME`
        return false;
    }
    else if (is_symbolic_arg(xt) || is_algebraic(xt))
    {
        algebraic_g zero = algebraic_p(integer::make(0));
        if (type == ID_polar)
            x = polar::make(x, zero, object::ID_PiRadians);
        else
            x = rectangular::make(x, zero);
        return +x;
    }

    return false;
}


bool algebraic::range_promotion(algebraic_g &x, object::id type)
// ----------------------------------------------------------------------------
//   Promote the value x to the given range type
// ----------------------------------------------------------------------------
{
    id xt = x->type();
    if (xt == type)
        return true;

    record(algebraic, "Range promotion of %p from %+s to %+s",
           (object_p) x, object::name(xt), object::name(type));

    if (!is_range(type))
    {
        record(algebraic_error, "Range promotion to invalid type %+s",
               object::name(type));
        return false;
    }

    // Can convert between ranges but not to/from uncertain
    if (is_range(xt))
        return (xt == ID_uncertain) == (type == ID_uncertain);

    // Symbolic values cannot be promoted to ranges
    if (is_symbolic(xt))
        return false;

    // Convert numerical values to uncertain range
    if (is_symbolic_arg(xt) || is_algebraic(xt))
    {
        if (type == ID_uncertain)
        {
            algebraic_g zero = integer::make(0);
            x = uncertain::make(x, zero);
        }
        else
        {
            x = range::make(type, x, x);
        }
        return +x;
    }

    return false;
}


object::id algebraic::bignum_promotion(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to the corresponding bignum
// ----------------------------------------------------------------------------
{
    id xt = x->type();
    id ty = xt;

    switch(xt)
    {
#if CONFIG_FIXED_BASED_OBJECTS
    case ID_hex_integer:        ty = ID_hex_bignum;     break;
    case ID_dec_integer:        ty = ID_dec_bignum;     break;
    case ID_oct_integer:        ty = ID_oct_bignum;     break;
    case ID_bin_integer:        ty = ID_bin_bignum;     break;
#endif // CONFIG_FIXED_BASED_OBJECTS
    case ID_based_integer:      ty = ID_based_bignum;   break;
    case ID_neg_integer:        ty = ID_neg_bignum;     break;
    case ID_integer:            ty = ID_bignum;         break;
    default:
        break;
    }
    if (ty != xt)
    {
        integer_g i = (integer *) object_p(x);
        x = rt.make<bignum>(ty, i);
    }
    return ty;
}


object::id algebraic::based_promotion(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to a based number
// ----------------------------------------------------------------------------
{
    if (!x)
        return object::ID_object;

    id xt = x->type();

    switch (xt)
    {
    case ID_integer:
    case ID_neg_integer:
        if (Settings.WordSize() < 64)
        {
            ularge value = integer_p(+x)->value<ularge>();
            if (xt == ID_neg_integer)
                value = -value;
            x = rt.make<based_integer>(value);
            return ID_based_integer;
        }
        else
        {
            xt = xt == ID_neg_integer ? ID_neg_bignum : ID_bignum;
            integer_g xi = integer_p(+x);
            bignum_g  xb = rt.make<bignum>(xt, xi);
            x = +xb;
        }
        // fallthrough

    case ID_bignum:
    case ID_neg_bignum:
    {
        size_t   sz   = 0;
        gcbytes  data = bignum_p(+x)->value(&sz);
        bignum_g xb   = rt.make<bignum>(ID_based_bignum, data, sz);
        if (xt == ID_neg_bignum)
        {
            bignum_g zero = rt.make<based_bignum>(0);
            xb = zero - xb;
        }
        x = +xb;
        return ID_based_bignum;
    }

    default:
        break;
    }
    return xt;
}


bool algebraic::to_integer(algebraic_g &x)
// ----------------------------------------------------------------------------
//  Check if we can convert the number to an integer (or big integer)
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    id ty = x->type();
    switch(ty)
    {
    case ID_hwfloat:
        x = hwfloat_p(+x)->to_integer();
        break;
    case ID_hwdouble:
        x = hwdouble_p(+x)->to_integer();
        break;
    case ID_decimal:
    case ID_neg_decimal:
        x = decimal_p(+x)->to_integer();
        break;

    case ID_integer:
    case ID_neg_integer:
    case ID_bignum:
    case ID_neg_bignum:
    case ID_fraction:
    case ID_neg_fraction:
    case ID_big_fraction:
    case ID_neg_big_fraction:
        break;

    case ID_unit:
        x = unit_p(+x)->map(to_integer);
        break;
    default:
        return false;
    }
    return x;                   // Need x to be non-null
}


// ============================================================================
//
//   to_fraction / to_quotient shared dispatch
//
// ============================================================================

struct to_fraction_context
// ----------------------------------------------------------------------------
//   Callbacks for real conversion and list mapping
// ----------------------------------------------------------------------------
{
    bool (*convert_real)(algebraic_g &);
    algebraic_p (*map_fn)(algebraic_r);
};


uint algebraic::fraction_digits(large exp10)
// ----------------------------------------------------------------------------
//   Significant digits shown for a value with given decimal exponent
// ----------------------------------------------------------------------------
//   STD and SIG show `DisplayDigits` significant digits, FIX n shows n
//   decimals (or n+1 significant digits when switching to an exponent),
//   SCI n and ENG n show n+1 significant digits. The result is capped by
//   `FractionDigits` and by the computation precision.
{
    large digits = Settings.DisplayDigits();
    large minsig = Settings.MinimumSignificantDigits();
    switch (Settings.DisplayMode())
    {
    case ID_Fix:
        if (minsig < 0 || digits + exp10 + 1 >= minsig)
            digits += exp10 + 1;
        else
            digits += 1;
        break;
    case ID_Sci:
    case ID_Eng:
        digits += 1;
        break;
    default:
        break;
    }
    large maxdig = Settings.FractionDigits();
    large prec   = large(Settings.Precision()) - 3;
    if (maxdig > prec)
        maxdig = prec;
    if (digits > maxdig)
        digits = maxdig;
    if (digits < 1)
        digits = 1;
    return digits;
}


static bool to_fraction_digits(algebraic_g &x, uint digits)
// ----------------------------------------------------------------------------
//   Convert hwfloat/hwdouble/decimal to fraction matching given digits
// ----------------------------------------------------------------------------
//   When `digits` is zero, use the number of digits being displayed
{
    object::id ty    = x->type();
    uint       count = Settings.FractionIterations();
    switch(ty)
    {
    case object::ID_hwfloat:
        x = hwfloat_p(+x)->to_fraction(count, digits);
        break;
    case object::ID_hwdouble:
        x = hwdouble_p(+x)->to_fraction(count, digits);
        break;
    case object::ID_decimal:
    case object::ID_neg_decimal:
        x = decimal_p(+x)->to_fraction(count, digits);
        break;
    case object::ID_integer:
    case object::ID_neg_integer:
    case object::ID_bignum:
    case object::ID_neg_bignum:
    case object::ID_fraction:
    case object::ID_neg_fraction:
    case object::ID_big_fraction:
    case object::ID_neg_big_fraction:
        return true;
    default:
        return false;
    }
    return x;
}


static bool to_fraction_real(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Convert hwfloat/hwdouble/decimal to fraction matching displayed digits
// ----------------------------------------------------------------------------
{
    return to_fraction_digits(x, 0);
}


static algebraic_p to_fraction_complex(algebraic_r re, algebraic_r im,
                                       bool ineg)
// ----------------------------------------------------------------------------
//   Build re±im·ⅈ, as an expression if a part is symbolic
// ----------------------------------------------------------------------------
//   A rectangular with an expression part, e.g. 1+'π'ⅈ, does not re-parse.
//   The imaginary part `im` is positive, `ineg` indicates its actual sign.
{
    if (!re || !im)
        return nullptr;
    if (re->is_real() && im->is_real())
        return rectangular::make(re, ineg ? algebraic_g(-im) : im);
    algebraic_g i = rectangular::make(integer::make(0), integer::make(1));
    algebraic_g ip = im->is_one(false) ? +i
        : algebraic_p(expression::make(object::ID_multiply, im, i));
    if (re->is_zero(false))
        return ineg ? expression::make(object::ID_neg, ip) : +ip;
    return expression::make(ineg ? object::ID_subtract : object::ID_add,
                            re, ip);
}


static bool to_fraction_dispatch(algebraic_g &x, const to_fraction_context &ctx)
// ----------------------------------------------------------------------------
//   Shared type switch; real types via callback, compound types recursed/mapped
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;
    object::id ty = x->type();
    switch(ty)
    {
    case object::ID_hwfloat:
    case object::ID_hwdouble:
    case object::ID_decimal:
    case object::ID_neg_decimal:
        return ctx.convert_real(x);

    case object::ID_integer:
    case object::ID_neg_integer:
    case object::ID_bignum:
    case object::ID_neg_bignum:
    case object::ID_fraction:
    case object::ID_neg_fraction:
    case object::ID_big_fraction:
    case object::ID_neg_big_fraction:
        break;

    case object::ID_rectangular:
    {
        rectangular_p z    = rectangular_p(+x);
        algebraic_g   re   = z->re();
        algebraic_g   im   = z->im();
        bool          ineg = im->is_negative(false);
        if (expression_p expr = im->as<expression>())
            if (object_p op = expr->outermost_operator())
                if (op->type() == object::ID_neg)
                    ineg = true;
        if (ineg)
            im = -im;
        algebraic_g   eps  = decimal::make(1, -int(Settings.FractionDigits()));
        if (smaller_magnitude(re, im * eps))
        {
            re = integer::make(0);
            if (!to_fraction_dispatch(im, ctx))
                return false;
            x = to_fraction_complex(re, im, ineg);
        }
        else if (smaller_magnitude(im, re * eps))
        {
            if (!to_fraction_dispatch(re, ctx))
                return false;
            x = re;
        }
        else
        {
            if (!to_fraction_dispatch(re, ctx) ||
                !to_fraction_dispatch(im, ctx))
                return false;
            x = to_fraction_complex(re, im, ineg);
        }
        break;
    }
    case object::ID_polar:
    {
        polar_p     z   = polar_p(+x);
        algebraic_g mod = z->mod();
        algebraic_g arg = z->pifrac();
        if (!to_fraction_dispatch(mod, ctx) || !to_fraction_dispatch(arg, ctx))
            return false;
        x = polar::make(mod, arg, object::ID_PiRadians);
        break;
    }
    case object::ID_range:
    case object::ID_drange:
    case object::ID_prange:
    case object::ID_uncertain:
    {
        range_p r = range_p(+x);
        algebraic_g lo = r->lo();
        algebraic_g hi = r->hi();
        if (!to_fraction_dispatch(lo, ctx) || !to_fraction_dispatch(hi, ctx))
            return false;
        x = range::make(r->type(), lo, hi);
        break;
    }
    case object::ID_unit:
        x = unit_p(+x)->map(ctx.map_fn);
        break;
    case object::ID_equation:
    {
        object_p inner = equation_p(+x)->value();
        if (!inner || !inner->is_algebraic())
            return false;
        x = algebraic_p(inner);
        // fall through
    }
    case object::ID_array:
    case object::ID_list:
    case object::ID_expression:
    {
        list_g mapped = list_p(+x)->map(ctx.map_fn);
        if (!mapped)
            return false;
        record(algebraic, "to_fraction mapped %p type %+s size %u",
               +mapped, object::name(mapped->type()), mapped->size());
        x = +mapped;
        break;
    }
    case object::ID_symbol:
    case object::ID_local:
        x = algebraic_p(+x)->evaluate();
        return x && to_fraction_dispatch(x, ctx);

    case object::ID_constant:
        // Leave constants as is
        return true;

    default:
        return false;
    }
    return x;
}


static algebraic_p to_fraction_map_fn(algebraic_r a)
// ----------------------------------------------------------------------------
//   Map callback for list::map in to_fraction
// ----------------------------------------------------------------------------
{
    algebraic_g ag = a;
    if (ag->is_algebraic_num())
        algebraic::to_fraction(ag);
    return +ag;
}


bool algebraic::to_fraction(algebraic_g &x)
// ----------------------------------------------------------------------------
//  Check if we can promote the number to a fraction
// ----------------------------------------------------------------------------
{
    to_fraction_context ctx = { to_fraction_real, to_fraction_map_fn };
    return to_fraction_dispatch(x, ctx);
}


algebraic_p algebraic::snap_near_integer(algebraic_r eps) const
// ----------------------------------------------------------------------------
//   Round to integer or bignum when the fractional part is below epsilon
// ----------------------------------------------------------------------------
{
    algebraic_g x = this;
    if (!x)
        return nullptr;

    id ty = x->type();
    if (is_integer(ty) || is_bignum(ty) || !is_real(ty))
        return x;

    algebraic_g frac = FracPart::evaluate(x);
    if (!frac)
        return x;
    if (frac->is_zero(false) || smaller_magnitude(frac, eps))
        algebraic::to_integer(x);
    return x;
}


algebraic_p algebraic::integer_sqrt(ularge value)
// ----------------------------------------------------------------------------
//   Build an expression for the square root of an integer
// ----------------------------------------------------------------------------
{
    if (value < 2)
        return integer::make(value);
    ularge sq = 0, rem = 0;
    extract_square_factor(value, sq, rem);
    algebraic_g result = integer::make(sq);
    if (rem > 1)
        result = result * expression::make(ID_sqrt, integer::make(rem));
    return result;
}


algebraic_p algebraic::symbolic_sqrt() const
// ----------------------------------------------------------------------------
//   Return a symbolic form for the square root
// ----------------------------------------------------------------------------
{
    algebraic_g x = this;
    if (x && x->is_fractionable() && Settings.SymbolicResults())
    {
        if (x->is_negative())
        {
            x = -x;
            x = x->symbolic_sqrt();
            return rectangular::make(integer::make(0), x);
        }

        if (integer_p i = x->as<integer>())
            return integer_sqrt(i->value<ularge>());
        if (bignum_p b = x->as<bignum>())
            return integer_sqrt(b->value<ularge>());
        if (x->is_fraction())
        {
            fraction_p f = fraction_p(+x);
            ularge num = f->numerator_value();
            ularge den = f->denominator_value();
            algebraic_g n = integer_sqrt(num);
            algebraic_g d   = integer_sqrt(den);
            return n / d;
        }
    }
    return sqrt::run(x);
}


// ============================================================================
//
//    Exact quotient
//
// ============================================================================

template <byte ...args>
constexpr byte eq<args...>::object_data[sizeof...(args)+2];

static ularge saturated_product(ularge a, ularge b)
// ----------------------------------------------------------------------------
//   Product of two unsigned values, saturating instead of overflowing
// ----------------------------------------------------------------------------
{
    if (a && b > ~ularge(0) / a)
        return ~ularge(0);
    return a * b;
}


static algebraic_p check_quotient_patterns(algebraic_r value,
                                           size_t       npats,
                                           const byte_p patterns[])
// ------------------------------------------------------------------------
//   Try the patterns, keep the simplest one that reproduces the value
// ------------------------------------------------------------------------
//   The plain fraction (as given by →Q) is the reference and fallback.
//   A pattern is accepted only if its value matches the input to the
//   displayed precision (or to the input's own digits if it has fewer), and
//   if its coefficients are simple enough that the match is not a mere
//   coincidence: any number matches some p/q to d digits with p·q ≈ 10^d,
//   so we require p·q ≤ 10^(d - D/2), where D is the displayed precision,
//   and p·q ≤ 10^(d-3) (but at least 2) so that a few digits are left
//   as evidence. The simplest result (smallest p·q) wins, earliest on ties.
{
    symbol_g    xx      = expression_p(x.as_bytes())->as_quoted<symbol>();
    symbol_g    pp      = expression_p(p.as_bytes())->as_quoted<symbol>();
    symbol_g    qq      = expression_p(q.as_bytes())->as_quoted<symbol>();
    symbol_g    ss      = expression_p(s.as_bytes())->as_quoted<symbol>();
    symbol_g    tt      = expression_p(t.as_bytes())->as_quoted<symbol>();
    algebraic_g best    = value;
    ularge      bestc   = ~ularge(0);
    algebraic_g numer   = nullptr;
    algebraic_g denom   = nullptr;
    algebraic_g unity   = integer::make(1);
    algebraic_g sq_s    = unity;
    algebraic_g sq_t    = unity;

    record(quotient, ">Check patterns for %t", +value);

    // Plain fraction first: it is the fallback, and it wins if integer
    if (!to_fraction_real(best) || !best)
        return nullptr;
    if (best->is_integer())
        return +best;
    object::id bty = best->type();
    if (bty == object::ID_fraction || bty == object::ID_neg_fraction)
    {
        fraction_p f = fraction_p(+best);
        bestc = saturated_product(f->numerator_value(),
                                  f->denominator_value());
    }
    record(quotient, "Plain fraction %t complexity %llu", +best, bestc);

    // Find the precision we need to match
    large exp10 = 0;
    uint  own   = ~0U;
    if (decimal_p d = value->as<decimal>())
    {
        exp10 = d->exponent() - 1;
        own   = d->significant_digits();
    }
    else if (hwdouble_p d = value->as<hwdouble>())
    {
        exp10 = large(std::floor(std::log10(d->value())));
    }
    else if (hwfloat_p d = value->as<hwfloat>())
    {
        exp10 = large(std::floor(std::log10(d->value())));
    }
    else
    {
        return +best;
    }
    uint  shown  = algebraic::fraction_digits(exp10);
    uint  digits = own < shown ? own : shown;
    large limexp = large(digits) - large(shown + 1) / 2;
    if (limexp < 0)
        return +best;
    if (limexp > large(digits) - 3)
        limexp = large(digits) - 3;
    if (limexp > 18)
        limexp = 18;
    ularge limit = 1;
    while (limexp-- > 0)
        limit *= 10;
    if (limit < 2)
        limit = 2;
    algebraic_g tol = decimal::make(5, exp10 - large(digits));
    record(quotient, "Matching %u digits (shown %u), limit %llu, tolerance %t",
           digits, shown, limit, +tol);

    for (size_t i = 0; i < npats; i += 2)
    {
        expression_p src = expression_p(patterns[i + 0]);
        algebraic_g  val = expression_p(src->substitute(xx, +value));
        if (!val || !algebraic::to_decimal(val, true) || rt.error())
        {
            rt.clear_error();
            continue;
        }
        record(quotient, "Pattern %t value %t", src, +val);
        // One digit of slack, since val and value may differ in magnitude.
        // The candidate is checked against the value below anyway.
        if (!to_fraction_digits(val, digits > 1 ? digits - 1 : 1) || !val)
            continue;
        if (val->is_fraction())
        {
            fraction_p frac = fraction_p(+val);
            numer           = bignum::smaller(frac->numerator());
            denom           = bignum::smaller(frac->denominator());
        }
        else
        {
            if (val->is_bignum())
                val = bignum::smaller(bignum_p(+val));
            numer = val;
            denom = unity;
        }
        if (!numer || !denom)
            return nullptr;
        record(quotient, "Fraction %t = %t/%t", +val, +numer, +denom);

        integer_p ip = numer->as_small_integer();
        integer_p iq = denom->as_small_integer();
        if (!ip || !iq || numer->is_zero() || denom->is_zero())
        {
            record(quotient, "Skipping, p is %t, q is %t", +numer, +denom);
            continue;
        }

        expression_p dst        = expression_p(patterns[i + 1]);
        bool         squares    = dst->contains(ss);
        bool         fractions  = dst->contains(pp);
        ularge       pv         = ip->value<ularge>();
        ularge       qv         = iq->value<ularge>();
        ularge       complexity = saturated_product(pv, qv);
        if (squares)
        {
            ularge ps, pr, qs, qr;
            extract_square_factor(pv, ps, pr);
            extract_square_factor(qv, qs, qr);
            sq_s       = fraction::make(ps, qs);
            sq_t       = fraction::make(pr, qr);
            denom      = integer::make(std::max(qr, qs));
            complexity = saturated_product(saturated_product(ps, qs),
                                           saturated_product(pr, qr));
            record(quotient, "Squares: p=%t s=%t q=%t t=%t",
                   +numer, +sq_s, +denom, +sq_t);
        }
        if (complexity > limit || complexity >= bestc)
        {
            record(quotient, "Skipping, complexity %llu", complexity);
            continue;
        }

        algebraic_g cand = squares
            ? expression_p(dst->substitute(ss, +sq_s, tt, +sq_t))
            : fractions
            ? expression_p(dst->substitute(pp, +numer, qq, +denom))
            : expression_p(dst->substitute(xx, +val));
        if (!cand)
            continue;
        if (object_p qo = expression_p(+cand)->quoted())
            if (algebraic_p qa = qo->as_algebraic())
                cand = qa;

        // Check that the candidate reproduces the input value
        algebraic_g num = cand;
        if (!algebraic::to_decimal(num, true) || rt.error() || !num)
        {
            rt.clear_error();
            continue;
        }
        algebraic_g diff = num - value;
        if (!diff || !diff->is_real() || smaller_magnitude(tol, diff))
        {
            record(quotient, "Rejecting %t, value %t", +cand, +num);
            continue;
        }

        best  = cand;
        bestc = complexity;
        record(quotient, "Best is %t", +best);
    }

    record(quotient, "<Got best match %t", +best);
    return +best;
}


template <typename... args>
algebraic_p check_quotient_patterns(algebraic_r value, args... rest)
// ----------------------------------------------------------------------------
//   Check a series of patterns and return the best match
// ----------------------------------------------------------------------------
{
    static constexpr byte_p rwdata[] = { rest.as_bytes()... };
    return check_quotient_patterns(value, sizeof...(rest), rwdata);
}


static bool to_sqrt_real(algebraic_g &value)
// ----------------------------------------------------------------------------
//   Convert real to fraction with π and √n
// ----------------------------------------------------------------------------
{
    if (!value)
        return false;
    bool neg = value->is_negative();
    if (neg)
        value = -value;
    algebraic_g r = check_quotient_patterns(value, sq(x), s*sqrt(t));
    if (r)
    {
        if (expression_p expr = r->as<expression>())
            r = expr->rewrites<expression::DOWN>(
                // Multiplicative simplifications
                k0 * x, k0,
                k1 * x, x,
                x * k0, k0,
                x * k1, x,
                k0 / x, k0,
                x / k1, x,
                x / x,   k1,
                x * (p/q), x*p/q,

                // Power simplifications
                sqrt(k1/x), sqrt(x)/x,
                sqrt(k1), k1,
                sqrt(k0), k0,
                k0^x, k0,
                k1^x, k1,
                x^k0, k1,
                x^k1, x);
        record(quotient, "Simplifies as %t", +r);
        if (r)
            value = neg ? -r : r;
    }
    return r;
}


static algebraic_p to_sqrt_map_fn(algebraic_r a)
// ----------------------------------------------------------------------------
//   Map callback for list::map in to_sqrt
// ----------------------------------------------------------------------------
{
    algebraic_g ag = a;
    if (ag->is_algebraic_num())
        algebraic::to_sqrt(ag);
    return +ag;
}


bool algebraic::to_sqrt(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Convert to fraction, trying π, √n, ln(n), and e as factors
// ----------------------------------------------------------------------------
{
    to_fraction_context ctx = { to_sqrt_real, to_sqrt_map_fn };
    return to_fraction_dispatch(x, ctx);
}


static bool to_quotient_real(algebraic_g &value)
// ----------------------------------------------------------------------------
//   Convert real to fraction with π, √n, ln(n), e factors (→Qπ)
// ----------------------------------------------------------------------------
{
    if (!value)
        return false;
    bool neg = value->is_negative();
    if (neg)
        value = -value;
    algebraic_g r = check_quotient_patterns(value,
                                            x/pi,       x*pi,
                                            x*pi,       p/(q*pi),
                                            pi/x,       q*pi/p,
                                            x/ln(k2),   x*ln(k2),
                                            x/ln(k3),   x*ln(k3),
                                            x/ln(k5),   x*ln(k5),
                                            x/ln(k7),   x*ln(k7),
                                            x/ln(k10),  x*ln(k10),
                                            x*ln(k2),   x/ln(k2),
                                            x*ln(k3),   x/ln(k3),
                                            x*ln(k5),   x/ln(k5),
                                            x*ln(k7),   x/ln(k7),
                                            x*ln(k10),  x/ln(k10),
                                            sq(x),      s*sqrt(t),
                                            exp(x),     ln(x),
                                            k2^x,       log2(x),
                                            k10^x,      log10(x),
                                            ln(x),      exp(x),
                                            log2(x),    k2^x,
                                            log10(x),   k10^x);
    if (r)
    {
        if (expression_p expr = r->as<expression>())
            r = expr->rewrites<expression::DOWN>(
                // Multiplicative simplifications
                k0 * x, k0,
                k1 * x, x,
                x * k0, k0,
                x * k1, x,
                k0 / x, k0,
                x / k1, x,
                x / x,   k1,
                x * (p/q), x*p/q,

                // Power simplifications
                sqrt(k1/x), sqrt(x)/x,
                sqrt(k1), k1,
                sqrt(k0), k0,
                k0^x, k0,
                k1^x, k1,
                x^k0, k1,
                x^k1, x);
        record(quotient, "Simplifies as %t", +r);
        if (r && neg)
            r = r->is_real() ? -r : expression::make(object::ID_neg, r);
        if (r)
            value = r;
    }
    return r;
}


static algebraic_p to_quotient_map_fn(algebraic_r a)
// ----------------------------------------------------------------------------
//   Map callback for list::map in to_quotient
// ----------------------------------------------------------------------------
{
    algebraic_g ag = a;
    if (ag->is_algebraic_num())
        algebraic::to_quotient(ag);
    return +ag;
}


bool algebraic::to_quotient(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Convert to fraction, trying π, √n, ln(n), and e as factors
// ----------------------------------------------------------------------------
{
    to_fraction_context ctx = { to_quotient_real, to_quotient_map_fn };
    return to_fraction_dispatch(x, ctx);
}


static algebraic_p to_decimal_callback(algebraic_r x, bool weak)
// ----------------------------------------------------------------------------
//  Callback for to_decimal applied to arrays
// ----------------------------------------------------------------------------
{
    algebraic_g v = x;
    return algebraic::to_decimal(v, weak) ? v : nullptr;
}


static algebraic_p to_decimal_strong(algebraic_r x)
// ----------------------------------------------------------------------------
//   For the string case (error emitting)
// ----------------------------------------------------------------------------
{
    return to_decimal_callback(x, false);
}


static algebraic_p to_decimal_weak(algebraic_r x)
// ----------------------------------------------------------------------------
//   For the weak case (no error emission)
// ----------------------------------------------------------------------------
{
    return to_decimal_callback(x, true);
}


bool algebraic::to_decimal(algebraic_g &x, bool weak)
// ----------------------------------------------------------------------------
//   Convert a value to decimal
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    id xt = x->type();

    switch(xt)
    {
    case ID_rectangular:
    {
        rectangular_p z = rectangular_p(+x);
        algebraic_g re = z->re();
        algebraic_g im = z->im();
        if (to_decimal(re, weak) && to_decimal(im, weak))
        {
            x = rectangular::make(re, im);
            return x;
        }
        break;
    }
    case ID_polar:
    {
        polar_p z = polar_p(+x);
        algebraic_g mod = z->mod();
        algebraic_g arg = z->pifrac();
        if (to_decimal(mod, weak) &&
            (mod->is_fraction() || to_decimal(arg, weak)))
        {
            x = polar::make(mod, arg, object::ID_PiRadians);
            return x;
        }
        break;
    }
    case ID_range:
    case ID_prange:
    case ID_drange:
    {
        range_p r = range_p(+x);
        algebraic_g lo = r->lo();
        algebraic_g hi = r->hi();
        if (to_decimal(lo, weak) && to_decimal(hi, weak))
        {
            x = range::make(r->type(), lo, hi);
            return true;
        }
        break;
    }
    case ID_uncertain:
    {
        uncertain_p u = uncertain_p(+x);
        algebraic_g a = u->average();
        algebraic_g s = u->stddev();
        if (to_decimal(a, weak) && to_decimal(s, weak))
        {
            x = uncertain::make(a, s);
            return true;
        }
        break;
    }
    case ID_unit:
        x = unit_p(+x)->map(weak ? to_decimal_weak : to_decimal_strong);
        return x;
    case ID_integer:
    case ID_neg_integer:
        if (weak)
            return true;
        // fallthrough
    case ID_bignum:
    case ID_neg_bignum:
    case ID_fraction:
    case ID_neg_fraction:
    case ID_big_fraction:
    case ID_neg_big_fraction:
    case ID_hwfloat:
    case ID_hwdouble:
    case ID_decimal:
    case ID_neg_decimal:
    case ID_True:
    case ID_False:
        return decimal_promotion(x);
    case ID_constant:
    case ID_standard_uncertainty:
    case ID_relative_uncertainty:
    case ID_xlib:
    {
        settings::SaveNumericalResults save(true);
        x = constant_p(+x)->evaluate();
        return x && !rt.error();
    }

    case ID_array:
    case ID_list:
        x = list_p(+x)->map(weak ? to_decimal_weak : to_decimal_strong);
        return x;

    case ID_symbol:
    case ID_local:
    case ID_Pi:
    case ID_EulerianNumber:
    case ID_Infinity:
    case ID_NegativeInfinity:
    case ID_expression:
        if (!unit::mode)
        {
            algebraic_p eq = algebraic_p(+x);
            settings::SaveNumericalResults save(true);
            x = eq->evaluate();
            return x && !rt.error();
        }
        // fallthrough
    default:
        if (!weak)
            rt.type_error();
    }
    return false;
}


bool algebraic::to_hwfloat(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to a hardware floating-point type if possible
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    id xt = x->type();
    record(algebraic, "Convert %p from %+s to hwfloat",
           (object_p) x, object::name(xt));

    switch(xt)
    {
    case ID_hwfloat:
        return true;
    case ID_hwdouble:
        x = hwfloat::make(hwdouble_p(+x)->as_float());
        return x;

    case ID_decimal:
    case ID_neg_decimal:
        x = hwfloat::make(decimal_p(+x)->to_float());
        return x;

    case ID_integer:
        x = as_hwfp(float(integer_p(+x)->value<ularge>()));
        return x;
    case ID_neg_integer:
        x = as_hwfp(-float(integer_p(+x)->value<ularge>()));
        return x;
    case ID_bignum:
    case ID_neg_bignum:
        x = decimal::from_bignum(bignum_p(+x));
        if (x && x->is_decimal())
            x = as_hwfp(decimal_p(+x)->to_float());
        return x;

    case ID_fraction:
        x = as_hwfp(float(fraction_p(+x)->numerator_value()) /
                    float(fraction_p(+x)->denominator_value()));
        return x;
    case ID_neg_fraction:
        x = as_hwfp(-float(fraction_p(+x)->numerator_value()) /
                    float(fraction_p(+x)->denominator_value()));
        return x;
    case ID_big_fraction:
    case ID_neg_big_fraction:
        x = decimal::from_big_fraction(big_fraction_p(+x));
        if (x && x->is_decimal())
                x = as_hwfp(decimal_p(+x)->to_float());
        return x;
    default:
        return false;
    }
}


bool algebraic::to_hwdouble(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Promote the value x to a hardware floating-point type if possible
// ----------------------------------------------------------------------------
{
    if (!x)
        return false;

    id xt = x->type();
    record(algebraic, "Convert %p from %+s to hwdouble",
           (object_p) x, object::name(xt));

    switch(xt)
    {
    case ID_hwfloat:
        x = hwfloat::make(hwfloat_p(+x)->as_double());
        return x;
    case ID_hwdouble:
        return true;

    case ID_decimal:
    case ID_neg_decimal:
        x = hwdouble::make(decimal_p(+x)->to_double());
        return x;

    case ID_integer:
        x = as_hwfp(double(integer_p(+x)->value<ularge>()));
        return x;
    case ID_neg_integer:
        x = as_hwfp(-double(integer_p(+x)->value<ularge>()));
        return x;
    case ID_bignum:
    case ID_neg_bignum:
        x = decimal::from_bignum(bignum_p(+x));
        if (x && x->is_decimal())
            x = as_hwfp(decimal_p(+x)->to_double());
        return x;

    case ID_fraction:
        x = as_hwfp(double(fraction_p(+x)->numerator_value()) /
                    double(fraction_p(+x)->denominator_value()));
        return x;
    case ID_neg_fraction:
        x = as_hwfp(-double(fraction_p(+x)->numerator_value()) /
                    double(fraction_p(+x)->denominator_value()));
        return x;
    case ID_big_fraction:
    case ID_neg_big_fraction:
        x = decimal::from_big_fraction(big_fraction_p(+x));
        if (x && x->is_decimal())
                x = as_hwfp(decimal_p(+x)->to_double());
        return x;
    default:
        return false;
    }
}


algebraic_g algebraic::pi()
// ----------------------------------------------------------------------------
//   Return the value of pi
// ----------------------------------------------------------------------------
{
    if (algebraic_p result = as_hwfp(M_PI))
        return result;
    return decimal::pi();
}


algebraic::angle_unit algebraic::adjust_angle(algebraic_g &x)
// ----------------------------------------------------------------------------
//   If we have an angle unit, use it for the computation
// ----------------------------------------------------------------------------
{
retry:
    angle_unit amode = ID_object;
    if (unit_p uobj = unit::get(x))
    {
        algebraic_g uexpr = uobj->uexpr();
        if (symbol_p sym = uexpr->as_quoted<symbol>())
        {
            if (sym->matches("dms") || sym->matches("°"))
                amode = ID_Deg;
            else if (sym->matches("r"))
                amode = ID_Rad;
            else if (sym->matches("pir") || sym->matches("πr"))
                amode = ID_PiRadians;
            else if (sym->matches("grad"))
                amode = ID_Grad;

        }
        if (amode == ID_object)
        {
            algebraic_g aunit = integer::make(1);
            if (add_angle(aunit))
                if (unit_p(+aunit)->convert(x, false))
                    goto retry;
        }
        if (amode)
            x = uobj->value();
    }
    return amode;
}


bool algebraic::add_angle(algebraic_g &x)
// ----------------------------------------------------------------------------
//   Add an angle unit if this is required
// ----------------------------------------------------------------------------
{
    cstring uname;

    switch(Settings.AngleMode())
    {
    case ID_Deg:        uname = "°";    break;
    case ID_Grad:       uname = "grad"; break;
    case ID_PiRadians:  uname = "πr";   break;
    case ID_Rad:        uname = "r";    break;
    default:
        return false;
    }

    symbol_p uexpr = symbol::make(uname);
    if (algebraic_p angle = unit::make(x, uexpr))
    {
        x = angle;
        return true;
    }
    return false;
}


algebraic_p algebraic::convert_angle(algebraic_r ra,
                                     angle_unit  from,
                                     angle_unit  to,
                                     bool        negmod,
                                     bool        domodulo)
// ----------------------------------------------------------------------------
//   Convert to angle in current angle mode.
// ----------------------------------------------------------------------------
//   If radians is set, input is in radians.
//   Otherwise, input is in fractions of pi (internal format for y() in polar).
{
    algebraic_g a = ra;
    if (a->is_real() && (from != to || negmod))
    {
        switch (from)
        {
        case ID_Deg:
            a = a / integer::make(180);
            break;
        case ID_Grad:
            a = a / integer::make(200);
            break;
        case ID_Rad:
        {
            algebraic_g pi = algebraic::pi();
            if (a->is_fraction())
            {
                fraction_g  f = fraction_p(+a);
                algebraic_g n = algebraic_p(f->numerator());
                algebraic_g d = algebraic_p(f->denominator());
                a = n / pi / d;
            }
            else
            {
                a = a / pi;
            }
            break;
        }
        case ID_PiRadians:
        default:
            break;
        }

        // Check if we have (-1, 0π), change it to (1, 1π)
        if (negmod)
            a = a + algebraic_g(integer::make(1));

        // Bring the result between -1 and 1
        algebraic_g one = integer::make(1);
        algebraic_g two = integer::make(2);
        if (domodulo)
        {
            a = (one - a) % two;
            if (!a)
                return nullptr;
            if (a->is_negative(false))
                a = a + two;
            a = one - a;
        }

        switch (to)
        {
        case ID_Deg:
            a = a * integer::make(180);
            break;
        case ID_Grad:
            a = a * integer::make(200);
            break;
        case ID_Rad:
        {
            algebraic_g pi = algebraic::pi();
            if (a->is_fraction())
            {
                fraction_g f = fraction_p(+a);
                algebraic_g n = algebraic_p(f->numerator());
                algebraic_g d = algebraic_p(f->denominator());
                a = pi * n / d;
            }
            else
            {
                a = a * pi;
            }
            break;
        }
        case ID_PiRadians:
        default:
            break;
        }
    }
    return a;
}


algebraic_p algebraic::exact_angle(int num, int denom, angle_unit aunit)
// ----------------------------------------------------------------------------
//   Generate a fraction of a turn in the given unit
// ----------------------------------------------------------------------------
{
    if (aunit != ID_Deg && aunit != ID_Grad && aunit != ID_PiRadians)
        return nullptr;

    int hturn = aunit == ID_Deg ? 180 : aunit == ID_Grad ? 200 : 1;
    num *= hturn;
    if (num % denom == 0)
        return integer::make(num/denom);
    return fraction::make(integer::make(num), integer::make(denom));
}


algebraic_p algebraic::evaluate_function(program_r eq, algebraic_r x)
// ----------------------------------------------------------------------------
//   Evaluate the eq object as a function
// ----------------------------------------------------------------------------
//   Equation objects can be one of:
//   - Something that takes value from the stack and returns it on the stack
//     for example << 1 + >>
//   - Something that evaluates using the indep and returns it on the stack,
//     for example 'X + 1' (assuming X is the independent variable)
{
    stack_depth_restore sdr;
    if (!rt.push(+x))
        return nullptr;
    rt.clear_error();
    save<object_g *> ival(expression::independent_value, (object_g *) &x);
    result           err    = eq->run();
    if (err != OK)
        return nullptr;

    object_p result = rt.pop();
    if (!result)
        return nullptr;

    size_t added = sdr.extra_depth();
    if (added == 1)
    {
        // Case where we evaluated from indep without consuming the stack
        object_p indep  = rt.pop();
        if (indep == +x)
            added = 0;
    }
    if (added != 0)
    {
        rt.invalid_function_error();
        return nullptr;
    }

    // Check that we have an acceptable return type
    if (!result->is_extended_algebraic())
    {
        rt.type_error();
        return nullptr;
    }

    return algebraic_p(result);
}


algebraic_p algebraic::evaluate_function(program_r   eq,
                                         algebraic_r x,
                                         algebraic_r y)
// ----------------------------------------------------------------------------
//   Evaluate the eq object as a function of two variables
// ----------------------------------------------------------------------------
{
    stack_depth_restore sdr;
    if (!rt.push(+x) || !rt.push(+y))
        return nullptr;
    rt.clear_error();
    save<object_g *> ival(expression::independent_value, (object_g *) &x);
    save<object_g *> dval(expression::dependent_value, (object_g *) &y);
    result           err    = eq->run();
    if (err != OK)
        return nullptr;

    object_p result = rt.pop();
    if (!result)
        return nullptr;

    size_t added   = sdr.extra_depth();
    if (added == 2)
    {
        // Case where we evaluated from indep without consuming the stack
        object_p dep  = rt.pop();
        object_p indep  = rt.pop();
        if (indep == +x && dep == +y)
            added = 1;
    }
    if (added != 1)
    {
        rt.invalid_function_error();
        return nullptr;
    }

    // Check that we have an acceptable return type
    if (!result->is_extended_algebraic())
    {
        rt.type_error();
        return nullptr;
    }
    return algebraic_p(result);
}


algebraic_p algebraic::evaluate() const
// ----------------------------------------------------------------------------
//   Evaluate an algebraic value as an algebraic
// ----------------------------------------------------------------------------
{
    stack_depth_restore sdr;
    if (program::run(this) != OK)
        return nullptr;

    if (rt.depth() != sdr.depth + 1)
    {
        rt.invalid_algebraic_error();
        return nullptr;
    }

    if (object_p obj = rt.pop())
    {
        while (tag_p tagged = obj->as<tag>())
            obj = tagged->tagged_object();
        if (obj->is_extended_algebraic())
            return algebraic_p(obj);
    }

    rt.type_error();
    return nullptr;
}


bool algebraic::is_numeric_constant() const
// ----------------------------------------------------------------------------
//  Return true if a value is a valid numerical constant in polynomials
// ----------------------------------------------------------------------------
{
    id ty = type();
    if (is_real(ty))
        return true;
    if (ty == ID_polar || ty == ID_rectangular)
    {
        complex_p z = complex_p(this);
        return z->x()->is_real() && z->y()->is_real();
    }
    return false;
}


algebraic_p algebraic::as_numeric_constant() const
// ----------------------------------------------------------------------------
//   Check if a value is a valid numerical constant (real or complex)
// ----------------------------------------------------------------------------
{
    if (is_numeric_constant())
        return this;
    return nullptr;
}


algebraic_p algebraic::zero_divide(algebraic_r x)
// ----------------------------------------------------------------------------
//   Deal with division by zero
// ----------------------------------------------------------------------------
{
    return rt.zero_divide(x && x->is_negative(false));
}


algebraic_p algebraic::epsilon(int impr)
// ----------------------------------------------------------------------------
//   Compute an epsilon value e.g. for numerical solver or integrator
// ----------------------------------------------------------------------------
{
    int         disp = Settings.DisplayDigits();
    int         prec = Settings.Precision();
    int         dig  = Settings.DisplayMode() == object::ID_Std
                           ? std::max(prec - impr, 3)
                           : std::min(disp + 1, std::max(prec - impr, 3));
    algebraic_p eps  = decimal::make(1, -dig);
    return eps;
}


int algebraic::compare(algebraic_r x, algebraic_r y)
// ----------------------------------------------------------------------------
//   Return a comparison number beteen two valeus
// ----------------------------------------------------------------------------
{
    int result;
    if (x && y && comparison::compare(&result, x, y))
        return result;
    return 777;
}


bool algebraic::list_result(uint depth, bool reverse)
// ----------------------------------------------------------------------------
//   For commands that give result in algebraic mode, return the list
// ----------------------------------------------------------------------------
{
    if (!in_expression)
        return true;
    scribble scr;
    for (uint d = 0; d < depth; d++)
    {
        object_p obj = rt.stack(reverse ? depth + ~d : d);
        if (!obj || !rt.append(obj))
            return false;
    }
    list_p result = list::make(ID_list, scr.scratch(), scr.growth());
    return result && rt.drop(depth) && rt.push(result);
}
