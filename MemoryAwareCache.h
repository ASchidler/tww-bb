
#ifndef TWW_BB_MEMORYAWARECACHE_H
#define TWW_BB_MEMORYAWARECACHE_H

#include "tww.h"
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <set>

#include <boost/functional/hash.hpp>


using namespace std;

namespace tww {
    template<typename T>
    struct VectorHash {
        std::size_t operator()(const vector<T>& f) const {
            return boost::hash_range(f.begin(), f.end());
        }
    };

    template<typename T>
    struct VectorEqual {
        bool operator()(const vector<T> &lhs, const vector<T> &rhs) const {
            if (lhs.size() != rhs.size())
                return false;
            for (auto i=0; i < lhs.size(); i++) {
                if (lhs[i] != rhs[i])
                    return false;
            }

            return true;
        }
    };

    template <
            class T,
            class Hash = std::hash<T>,
            class KeyEqual = std::equal_to<T>
    >
    class MemoryAwareCache {
    private:
        unordered_map<T, size_t, Hash, KeyEqual> _cache;
        size_t c_counter = 0;
        multiset<size_t, std::greater<>> sizes;
        size_t maximum;
    public:
        explicit MemoryAwareCache(size_t maximum) : maximum(maximum) {
            _cache.reserve(maximum);
        }

        size_t get_size() {
            return _cache.size();
        }

        size_t get_buckets() {
            return _cache.bucket_count();
        }

        bool get(T& val) {
            auto tg = _cache.find(val);

            if (tg == _cache.end())
                return false;

            tg->second = c_counter++;
            return true;
        }

        void set(T val) {
            if (_cache.size() >= maximum) {
                size_t target = _cache.size() / 2;
                sizes.clear();

                for(auto& ce: _cache) {
                    sizes.insert(ce.second);
                    if (sizes.size() > target)
                        sizes.erase(sizes.begin());
                }

                size_t c_minimum = *sizes.begin();

                for(auto it=_cache.begin(); it != _cache.end();) {
                    if (it->second <= c_minimum) {
                        auto td = it;
                        ++it;
                        _cache.erase(td);
                    } else {
                        ++it;
                    }
                }
            }
            _cache.emplace(std::move(val), c_counter++);
        }
    };
}

#endif //TWW_BB_MEMORYAWARECACHE_H
