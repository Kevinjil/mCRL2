#ifndef SIP_COMMAND_LINE_INTERFACE_H
#define SIP_COMMAND_LINE_INTERFACE_H

#include <boost/shared_ptr.hpp>
#include <boost/noncopyable.hpp>

#include <sip/tool.h>

namespace sip {

  namespace cli {

    /** \brief Convenience type for hiding boost shared pointers */
    typedef boost::shared_ptr < sip::scheme > scheme_ptr;

    /**
     * This class provides functionality to extract protocol specific arguments
     * from the list of command line arguments that a tool receives.
     **/
    class command_line_argument_extractor : public boost::noncopyable {
      private:

        /** The list of known of options */
        static const char*  known_options[];

        /** The list of known of schemes */
        static const char*  known_schemes[];

        /** The number of options in known_options[] */
        static const size_t known_option_number;

        /** The number of schemes in known_schemes[] */
        static const size_t known_scheme_number;

        /** \brief The number of the last matched known_option or known_scheme. */
        size_t last_matched;

        /** \brief Parses a minimum prefix of argument to search for a known option */
        inline char* parse_option(char* const);

        /** \brief Parses a minimum prefix of argument to search for a known scheme */
        inline char* parse_scheme(char* const) throw ();

        /** \brief the scheme that was last parsed succesfully */
        scheme_ptr   selected_scheme;

        /** A unique number that identifies this instance */
        long int identifier;

      public:

        /** \brief Constructor that performs extraction */
        inline command_line_argument_extractor(int&, char** const) throw ();

        /** \brief Removes protocol specific options and adjusts the argument count */
        inline void process(int&, char** const) throw ();

        /** \brief Get the arguments for the selected scheme */
        inline scheme_ptr get_scheme() const;

        /** \brief Get the identifier */
        inline long get_identifier() const;
    };

    /** Constructor */
    inline command_line_argument_extractor::command_line_argument_extractor(int& argc, char** const argv) throw () : identifier(-1) {
      process(argc, argv);
    }
  }
}
#endif
