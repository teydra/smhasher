"""Small fixed-width integer helpers shared by the attacks (all values are Python ints)."""


def mask(bits):
    return (1 << bits) - 1


def inv(a, bits):
    """Multiplicative inverse of an odd constant modulo 2^bits."""
    return pow(a, -1, 1 << bits)


def rotl(x, r, bits):
    r %= bits
    return ((x << r) | (x >> (bits - r))) & mask(bits)


def rotr(x, r, bits):
    return rotl(x, bits - (r % bits), bits)


def unxorshr(y, s, bits):
    """x with y = x ^ (x >> s)."""
    x = y
    for _ in range(bits // s + 1):
        x = y ^ (x >> s)
    return x & mask(bits)


def unxorshl(y, s, bits):
    """x with y = x ^ (x << s) (mod 2^bits)."""
    x = y
    for _ in range(bits // s + 1):
        x = (y ^ (x << s)) & mask(bits)
    return x


def le(x, nbytes):
    return (x & mask(8 * nbytes)).to_bytes(nbytes, "little")


def from_le(b):
    return int.from_bytes(b, "little")
