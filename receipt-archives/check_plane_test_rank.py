"""Check the two-row weight decomposition and the finite rank counts."""

from math import comb


def determinant(matrix):
    """Fraction-free elimination over the integers."""
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for i in range(len(a)-1):
        pivot_row = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot_row is None:
            return 0
        if pivot_row != i:
            a[i], a[pivot_row] = a[pivot_row], a[i]
            sign = -sign
        pivot = a[i][i]
        for j in range(i+1, len(a)):
            for k in range(i+1, len(a)):
                value = pivot * a[j][k] - a[j][i] * a[i][k]
                quotient, remainder = divmod(value, previous)
                assert remainder == 0
                a[j][k] = quotient
            a[j][i] = 0
        previous = pivot
    return sign*a[-1][-1]


def component_column(N, j, total):
    """Column at total second-coordinate degree 'total', indexed by z2 degree."""
    D = N-j
    result = [0]*(N+1)
    for a in range(D+1):
        b = total-j-a
        if not 0 <= b <= D:
            continue
        for t in range(j+1):
            result[a+t] += (-1)**t * comb(j, t) * comb(D, a) * comb(D, b)
    return result[max(0,total-N):min(N,total)+1]


def check_basis():
    for N in range(1, 11):
        count = 0
        for weight in range(2*N+1):
            columns = [component_column(N, j, weight)
                       for j in range(min(weight, 2*N-weight)+1)]
            assert len(columns) == len(columns[0])
            assert determinant(columns) != 0
            count += len(columns)
        assert count == (N+1)**2


def count_bounds(N, slack, c):
    assert 0 <= slack-12*c <= slack+12*c < N
    return (slack-12*c+1)**2, (slack+12*c+1)**2, (N+1)**2


if __name__ == "__main__":
    check_basis()
    low, high, total = count_bounds(79000, 54001, 1000)
    assert (low, high, total) == (1764168004, 4356264004, 6241158001)
    assert total-high == 1884893997
    print("Exact integer basis checks passed in all torus weights for N=1 through 10.")
    print(f"{low} <= surviving rank <= {high} out of {total}.")
    p = 79
    for m in (3, 6, 12):
        N = 2*p**m
        c = 1000*(m+1)
        slack = (2*(N+2) + p-1)//p + 52*c
        low, high, total = count_bounds(N, slack, c)
        print(f"m={m}: {low/total:.11f} <= fraction <= {high/total:.11f}")
    print(f"The analytical limit is 4/{p**2}.")
