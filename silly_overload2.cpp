#include <utility>
#include <type_traits>
#include <cstddef>
#include <new>
#include <string>

template<typename...Ts>
struct TypeList {
    static constexpr size_t size = sizeof...(Ts);
};

template<size_t Is, typename T>
struct ErasedTupleLeaf {
    T value;

    template<typename U>
    ErasedTupleLeaf(U&& v) noexcept(std::is_nothrow_constructible_v<T, U>)
        : value(std::forward<U>(v)) {}
    friend T Get(ErasedTupleLeaf& self, std::integral_constant<size_t, Is>) noexcept {
        return std::move(self.value);
    }
};

template<size_t Is, typename T>
struct ErasedTupleLeaf<Is, T&> {
    T* value;

    ErasedTupleLeaf(T& r) noexcept : value(&r) {}
    friend T& Get(ErasedTupleLeaf& self, std::integral_constant<size_t, Is>) noexcept {
        return *self.value;
    }
};

template<typename T, typename...Args>
struct _ErasedTuple;

template<size_t...Is, typename...Args>
struct _ErasedTuple<std::index_sequence<Is...>, Args...> : ErasedTupleLeaf<Is, Args>...
{
    template<typename...A>
    _ErasedTuple(A&&...a) :
        ErasedTupleLeaf<Is, Args>(std::forward<A>(a))...
    {}
};

template<typename...Args>
using ErasedTuple = _ErasedTuple<std::make_index_sequence<sizeof...(Args)>, Args...>;

template<typename...Args>
constexpr size_t erased_tuple_size_of(TypeList<Args...>) {
    return sizeof(ErasedTuple<Args...>);
}

template<typename...Args, typename...Passed>
void* erased_tuple_emplace(TypeList<Args...>, void* data, Passed&&...args) {
    return new(data) ErasedTuple<Args...>(std::forward<Passed>(args)...);
}

template<typename...Args>
void erased_tuple_destroy(TypeList<Args...>, void* data) noexcept {
    using Tuple = ErasedTuple<Args...>;
    static_cast<Tuple*>(data)->~Tuple();
}

template<size_t I, typename...Args>
decltype(auto) erased_tuple_get(TypeList<Args...>, void* data) {
    using Tuple = ErasedTuple<Args...>;
    return Get(*static_cast<Tuple*>(data), std::integral_constant<size_t, I>{});
}

struct Arg {
    int self{};
    template<typename T> bool get(T& v);
    template<typename T> void set(T);
};

template<typename T>
constexpr size_t _hash_type() {
    const char* src =
#ifdef _MSC_VER
        __FUNCSIG__;
#else
        __PRETTY_FUNCTION__;
#endif
    size_t result = 5381;
    char ch{};
    while((ch = *src++)) {
        result += result * 33 ^ ch;
    }
    return result;
}

template<size_t pos, typename Head, typename...Tail>
auto arg_at_pos(TypeList<Head, Tail...>) {
    if constexpr (!pos) return Head{};
    else {
        static_assert(sizeof...(Tail));
        return arg_at_pos<pos - 1>(TypeList<Tail...>{});
    }
}

template<typename P, typename F>
struct SeparationResult {
    using pass = P;
    using fail = F;
};

template<typename Pred, class...p, class...f>
auto SeparateLists(TypeList<>, TypeList<p...>, TypeList<f...>)
    -> SeparationResult<TypeList<p...>, TypeList<f...>>;

template<typename Pred, class head, class...tail, class...p, class...f>
auto SeparateLists(TypeList<head, tail...>, TypeList<p...>, TypeList<f...>) {
    if constexpr (Pred::check(head{})) {
        return SeparateLists<Pred>(
            TypeList<tail...>{}, TypeList<p..., head>{}, TypeList<f...>{});
    } else {
        return SeparateLists<Pred>(
            TypeList<tail...>{}, TypeList<p...>{}, TypeList<f..., head>{});
    }
}

// resulting type has two typedefs
// pass: all signatures passing predicate
// fail: all signatures failing predicate
template<typename Pred, typename Set>
using separated_t = decltype(SeparateLists<Pred>(Set{}, TypeList<>{}, TypeList<>{}));

template<size_t pos, typename T>
struct SameArgAtPos {
    template<typename Other>
    static constexpr bool check(Other) {
        return std::is_same_v<T, decltype(arg_at_pos<pos>(Other{}))>;
    }
};

template<typename T, typename...Tail>
auto first(TypeList<T, Tail...>) -> T;

template<typename...Signatures>
constexpr bool conflicting_overloads = false;

template<size_t argc, size_t pos, class Pivot, class...Same, class...Other, class...Ready>
size_t choose_overload(
    void** out, Arg* args,
    TypeList<Pivot, Same...> match,
    TypeList<Other...> miss,
    Ready&...ready)
{
    using CurrentArg = decltype(arg_at_pos<pos>(Pivot{}));
    CurrentArg arg;
    if (args[pos].get(arg)) {
        if constexpr (pos == argc - 1) {
            if constexpr (sizeof...(Same)) {
                static_assert(conflicting_overloads<Pivot, Same...>);
            }
            *out = erased_tuple_emplace(Pivot{}, *out, std::move(ready)..., std::move(arg));
            return _hash_type<Pivot>();
        } else {
            using NextArg = decltype(arg_at_pos<pos + 1>(Pivot{}));
            using Next = separated_t<SameArgAtPos<pos + 1, NextArg>, TypeList<Pivot, Same...>>;
            return choose_overload<argc, pos + 1>(
                out, args, typename Next::pass{}, typename Next::fail{}, ready..., arg);
        }
    } else if constexpr (miss.size) {
        using NewPivot = decltype(first(TypeList<Other...>{}));
        using ChangeArg = decltype(arg_at_pos<pos>(NewPivot{}));
        using ChangePivot = separated_t<SameArgAtPos<pos, ChangeArg>, TypeList<Other...>>;
        return choose_overload<argc, pos>(
            out, args, typename ChangePivot::pass{}, typename ChangePivot::fail{}, ready...);
    } else {
        return 0;
    }
}

template<typename T> struct inspect_method;
template<typename R, typename T, typename...A>
struct inspect_method<R(T::*)(A...)>
{
    using Ret = R;
    using Cls = T;
    using Args = TypeList<A...>;
};

template<auto...methods>
struct OverloadSet {
    static constexpr size_t size = sizeof...(methods);
};

template<size_t argc>
struct CanBeCalledWith {
    template<typename...Args>
    static constexpr size_t check(TypeList<Args...> args) {
        return args.size == argc;
    }
};

template<typename R, typename T, typename...Args, size_t...Is>
bool do_call(
    Arg* out, size_t signatureHash, void* super_tuple,
    T* self, R(T::*method)(Args...), std::index_sequence<Is...>
    )
{
    using Signature = TypeList<Args...>;
    constexpr size_t selfHash = _hash_type<Signature>();
    if (signatureHash == selfHash) {
        try {
            if constexpr (std::is_void_v<R>) {
                (self->*method)(erased_tuple_get<Is>(Signature{}, super_tuple)...);
            } else {
                auto r = (self->*method)(erased_tuple_get<Is>(Signature{}, super_tuple)...);
                if (out) out->set(std::move(r));
            }
            erased_tuple_destroy(Signature{}, super_tuple);
            return true;
        } catch (...) {
            erased_tuple_destroy(Signature{}, super_tuple);
            throw;
        }
    } else {
        return false;
    }
}

template<typename T, typename...Ts>
constexpr auto max_of(T first, Ts...v) {
    auto result = first;
    ((v > result && (result = v)), ...);
    return result;
}

template<size_t...Is, typename Fn>
constexpr void const_for_each(std::index_sequence<Is...>, Fn f) {
    (f(std::integral_constant<size_t, Is>{}), ...);
}

template<auto m>
using args_of = typename inspect_method<decltype(m)>::Args;

constexpr bool _check_signatures(const size_t* hashes, size_t count) {
    auto end = hashes + count;
    for (auto i = hashes; i != end; ++i) {
        if (!*i) return false;
        for (auto j = i + 1; j != end; ++j) {
            if (*i == *j) return false;
        }
    }
    return true;
}

template<typename T, auto...methods>
void call(Arg* out, T* self, Arg* args, size_t size, OverloadSet<methods...>) {
    constexpr size_t methods_count = sizeof...(methods);
    static_assert(methods_count, "Empty overload set");
    constexpr size_t max_args = max_of(args_of<methods>::size...);
    using ArgsListList = TypeList<args_of<methods>...>;
    constexpr size_t all_hashes[] = {_hash_type<args_of<methods>>()...};
    static_assert(_check_signatures(all_hashes, methods_count),
                  "Invalid overload signatures: Collisions found");
    constexpr auto storage_size = max_of(erased_tuple_size_of(
        typename inspect_method<decltype(methods)>::Args{})...);
    alignas(std::max_align_t) char storage[storage_size];
    void* storage_ptr = &storage;
    void** erased_args = &storage_ptr;
    size_t chosen_hash = 0; //hash for any signature must not be '0'
    // lambda will be called with std::integral_constant<size_t, i>
    // for i = 0; i < max_args; ++i
    const_for_each(std::make_index_sequence<max_args + 1>(), [&](auto argc){
        if (!chosen_hash && size == argc.value) {
            using Callable = typename separated_t<CanBeCalledWith<argc.value>, ArgsListList>::pass;
            if constexpr (Callable::size) {
                if constexpr (!argc.value) {
                    static_assert(Callable::size == 1 || conflicting_overloads<Callable>);
                    using Method = decltype(first(Callable{}));
                    *erased_args = erased_tuple_emplace(Method{}, *erased_args);
                    chosen_hash = _hash_type<Method>();
                } else {
                    using First = decltype(first(Callable{}));
                    using Arg0 = decltype(arg_at_pos<0>(First{}));
                    using InitialSplit = separated_t<SameArgAtPos<0, Arg0>, Callable>;
                    chosen_hash = choose_overload<argc, 0>(
                        erased_args, args, typename InitialSplit::pass{}, typename InitialSplit::fail{});
                }
            } else {
                throw "Error: not overload for such argument count";
            }
        }
    });
    if (chosen_hash) {
        (do_call(out, chosen_hash, *erased_args, self, methods, std::make_index_sequence<args_of<methods>::size>()) || ...);
    } else {
        throw "Error: could not match any overload";
    }
}

template<typename T>
bool Arg::get(T& v) {
    static int lol = 0;
    v = lol++;
    return true;
}

template<typename T>
void Arg::set(T v) {
    self = v;
}

struct Victim {
    int a(int x) {
        return x;
    }
    int b(int x, int y) {
        return x + y;
    }
    int c(bool x) {
        return x ? 1 : -1;
    }
    int d() {
        return 1;
    }
};

int main()
{
    Arg out;
    Arg args[5] = {};
    using Overloads = OverloadSet<&Victim::a, &Victim::b, &Victim::c, &Victim::d>;
    Victim obj;
    call(&out, &obj, args, 0, Overloads{});
    call(&out, &obj, args, 1, Overloads{});
    call(&out, &obj, args, 2, Overloads{});
    return 0;
}
