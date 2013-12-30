#include "crv.h"

namespace crv
{

const std::string Tracer::s_value_prefix = "v!";
const std::string Encoder::s_time_prefix = "t!";
const std::string Encoder::s_rf_prefix = "rf!";
const std::string Encoder::s_pf_prefix = "pf!";
const std::string Encoder::s_ldf_prefix = "ldf!";

Tracer& tracer() {
  static Tracer s_tracer;
  return s_tracer;
}

}
