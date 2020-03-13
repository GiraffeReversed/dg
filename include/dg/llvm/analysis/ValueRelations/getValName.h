#ifndef _DG_LLVM_GET_VAL_NAME_H_
#define _DG_LLVM_GET_VAL_NAME_H_

#include <iostream>
#include <sstream>
#include <fstream>
#include <string>
#include <llvm/Support/raw_os_ostream.h>

namespace dg{
namespace debug {
inline std::string getValName(const llvm::Value *val) {
    std::ostringstream ostr;
    llvm::raw_os_ostream ro(ostr);

    assert(val);
    ro << *val;
    ro.flush();

    std::string result = ostr.str();
    auto it = result.begin();
    while (it != result.end() && *it == ' ') it = result.erase(it);

    // break the string if it is too long
    return result;
}

inline std::string getTypeName(const llvm::Type* type) {
    std::ostringstream ostr;
    llvm::raw_os_ostream ro(ostr);

    assert(type);
    ro << *type;
    ro.flush();

    std::string result = ostr.str();
    auto it = result.begin();
    while (it != result.end() && *it == ' ') it = result.erase(it);

    // break the string if it is too long
    return result;  
}

} // namespace debug
} // namespace dg

#endif // _DG_LLVM_GET_VAL_NAME_H_
